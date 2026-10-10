import importlib.util
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import threading
import time
import unittest

HERE = Path(__file__).resolve().parent
SOURCE = HERE / "verify-dft-model-components.py"
spec = importlib.util.spec_from_file_location("scheduler", SOURCE)
scheduler = importlib.util.module_from_spec(spec)
spec.loader.exec_module(scheduler)


def running(pid):
    result = subprocess.run(["ps", "-o", "stat=", "-p", str(pid)], capture_output=True, text=True)
    return result.returncode == 0 and not result.stdout.strip().startswith("Z")


def await_file(path):
    deadline = time.monotonic() + 10
    while not path.is_file():
        if time.monotonic() >= deadline:
            raise AssertionError(f"Missing fixture marker: {path}")
        time.sleep(0.01)


class SchedulerTests(unittest.TestCase):
    def test_dependency_order_and_worker_limit(self):
        for jobs in (1, 3):
            with self.subTest(jobs=jobs), tempfile.TemporaryDirectory() as directory:
                path = Path(directory)
                dependencies = {"a": set(), "b": set(), "c": {"a"}, "d": {"b", "c"}}
                lock, active, maximum = threading.Lock(), 0, 0
                processes = scheduler.BuildProcesses()

                def compile_one(name):
                    nonlocal active, maximum
                    self.assertTrue(all((path / dep).exists() for dep in dependencies[name]))
                    with lock:
                        active += 1
                        maximum = max(maximum, active)
                    process = processes.start([sys.executable, "-c",
                        "import pathlib,sys,time;time.sleep(.1);pathlib.Path(sys.argv[1]).write_text('done')",
                        str(path / name)], start_new_session=True)
                    try:
                        self.assertEqual(process.wait(), 0)
                    finally:
                        processes.discard(process)
                        with lock:
                            active -= 1

                scheduler.dependency_builds(list(dependencies), dependencies, compile_one, jobs, processes.cancel)
                self.assertEqual(set(p.name for p in path.iterdir()), set(dependencies))
                self.assertLessEqual(maximum, jobs)
                self.assertEqual(maximum, 1 if jobs == 1 else 2)

    def test_failure_reaps_worker_and_descendant(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            processes = scheduler.BuildProcesses()
            owned = []

            def compile_one(name):
                if name == "fail":
                    await_file(path / "grandchild")
                    raise RuntimeError("expected compiler failure")
                child = "import os,pathlib,signal,sys,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);pathlib.Path(sys.argv[1]).write_text(str(os.getpid()));time.sleep(60)"
                parent = "import pathlib,subprocess,sys,time;subprocess.Popen([sys.executable,'-c',sys.argv[1],sys.argv[2]]);time.sleep(60)"
                process = processes.start([sys.executable, "-c", parent, child, str(path / "grandchild")], start_new_session=True)
                owned.append(process.pid)
                try:
                    process.wait()
                finally:
                    processes.discard(process)

            with self.assertRaisesRegex(RuntimeError, "expected compiler failure"):
                scheduler.dependency_builds(["worker", "fail"], {"worker": set(), "fail": set()}, compile_one, 2, processes.cancel)
            owned.append(int((path / "grandchild").read_text()))
            self.assertTrue(all(not running(pid) for pid in owned))
            self.assertFalse(processes.active)

    def test_sigterm_cancels_all_workers(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            driver = r'''
import importlib.util,pathlib,signal,sys
spec=importlib.util.spec_from_file_location('scheduler',sys.argv[1]);s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s)
signal.signal(signal.SIGTERM,lambda sig,frame:(_ for _ in ()).throw(SystemExit(128+sig)))
owner=s.BuildProcesses();directory=pathlib.Path(sys.argv[2])
def compile_one(name):
 p=owner.start([sys.executable,'-c','import os,pathlib,sys,time;pathlib.Path(sys.argv[1]).write_text(str(os.getpid()));time.sleep(60)',str(directory/name)],start_new_session=True)
 try:p.wait()
 finally:owner.discard(p)
s.dependency_builds(['a','b'],{'a':set(),'b':set()},compile_one,2,owner.cancel)
'''
            process = subprocess.Popen([sys.executable, "-c", driver, str(SOURCE), str(path)])
            try:
                await_file(path / "a")
                await_file(path / "b")
                pids = [int((path / name).read_text()) for name in ("a", "b")]
                process.send_signal(signal.SIGTERM)
                self.assertEqual(process.wait(timeout=10), 143)
                self.assertTrue(all(not running(pid) for pid in pids))
            finally:
                if process.poll() is None:
                    process.kill()
                    process.wait()

    def test_failed_logged_compiler_cleans_its_descendant(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            old_cwd = scheduler.LEAN
            scheduler.LEAN = path
            try:
                for warning in (False, True):
                    with self.subTest(warning=warning):
                        marker = path / str(warning)
                        child = "import os,pathlib,signal,sys,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);pathlib.Path(sys.argv[1]).write_text(str(os.getpid()));time.sleep(60)"
                        parent = "import pathlib,subprocess,sys,time;subprocess.Popen([sys.executable,'-c',sys.argv[1],sys.argv[2]]);p=pathlib.Path(sys.argv[2]);exec('while not p.exists():time.sleep(.01)');print('warning: fixture' if sys.argv[3]=='True' else 'failed fixture');sys.exit(0 if sys.argv[3]=='True' else 1)"
                        owner = scheduler.BuildProcesses()
                        with self.assertRaises(AssertionError):
                            scheduler.run_logged([sys.executable, "-c", parent, child, str(marker), str(warning)], path / "failed.log", processes=owner)
                        self.assertFalse(running(int(marker.read_text())))
                        self.assertFalse(owner.active)
            finally:
                scheduler.LEAN = old_cwd

    def test_repeated_sigterm_during_cleanup(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            driver = r'''
import importlib.util,pathlib,signal,sys
spec=importlib.util.spec_from_file_location('verifier',sys.argv[1]);s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s)
signal.signal(signal.SIGTERM,lambda sig,frame:(_ for _ in ()).throw(SystemExit(128+sig)))
owner=s.BuildProcesses();directory=pathlib.Path(sys.argv[2])
def compile_one(name):
 p=owner.start([sys.executable,'-c','import os,pathlib,signal,sys,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);pathlib.Path(sys.argv[1]).write_text(str(os.getpid()));time.sleep(60)',str(directory/name)],start_new_session=True)
 try:p.wait()
 finally:owner.discard(p)
s.dependency_builds(['a'],{'a':set()},compile_one,1,owner.cancel)
'''
            process = subprocess.Popen([sys.executable, "-c", driver, str(SOURCE), str(path)])
            try:
                await_file(path / "a")
                child = int((path / "a").read_text())
                process.send_signal(signal.SIGTERM)
                time.sleep(0.1)
                process.send_signal(signal.SIGTERM)
                self.assertEqual(process.wait(timeout=15), 143)
                self.assertFalse(running(child))
            finally:
                if process.poll() is None:
                    process.kill()
                    process.wait()

    def test_repeated_sigterm_waiting_for_start_lock(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            driver = r'''
import importlib.util,pathlib,signal,sys,time
spec=importlib.util.spec_from_file_location('verifier',sys.argv[1]);s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s)
signal.signal(signal.SIGTERM,s.termination_requested)
owner=s.BuildProcesses();directory=pathlib.Path(sys.argv[2])
def compile_one(name):
 p=owner.start([sys.executable,'-c','import time;time.sleep(60)'],start_new_session=True)
 try:
  with owner.lock:
   (directory/'locked').write_text(str(p.pid));time.sleep(.5)
  p.wait()
 finally:owner.discard(p)
s.dependency_builds(['a'],{'a':set()},compile_one,1,owner.cancel)
'''
            process = subprocess.Popen([sys.executable, "-c", driver, str(SOURCE), str(path)])
            try:
                await_file(path / "locked")
                child = int((path / "locked").read_text())
                process.send_signal(signal.SIGTERM)
                time.sleep(0.05)
                process.send_signal(signal.SIGTERM)
                self.assertEqual(process.wait(timeout=5), 143)
                self.assertFalse(running(child))
            finally:
                if process.poll() is None:
                    process.kill()
                    process.wait()

    def test_invalid_graph_and_parallelism_fail(self):
        for ordered, dependencies, jobs in [(["a"], {"a": {"missing"}}, 1), (["a"], {"a": {"a"}}, 1), (["a"], {"a": set()}, 0)]:
            with self.subTest(dependencies=dependencies, jobs=jobs):
                with self.assertRaises((AssertionError, ValueError)):
                    scheduler.dependency_builds(ordered, dependencies, lambda _: self.fail("invalid graph started a build"), jobs, lambda: None)


if __name__ == "__main__":
    unittest.main()
