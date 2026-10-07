#!/usr/bin/env python3
"""Bounded controller for one staged projected CUDA sweep; retain terminal state."""
import argparse
from datetime import datetime,timezone
import json
import os
from pathlib import Path
import platform
import signal
import subprocess
import sys
import time


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,required=True)
    parser.add_argument('--bits',type=int,choices=(6,8),required=True)
    parser.add_argument('--timeout',type=float,default=240)
    args=parser.parse_args()
    root=args.root.resolve();case=root/f'bits{args.bits}'
    output=case/'gpu';output.mkdir(parents=True,exist_ok=True)
    log=output/'run.log';terminal=output/'terminal.json'
    command=[sys.executable,'-I','-u',str(root/'scripts/check-projected-cuda.py'),
             '--program',str(case/'program.json'),'--fixture',str(case/'fixture.npz'),
             '--output-prefix',str(output/'sweep'),'--timeout','180']
    started=time.monotonic()
    receipt={'schema':'projected-cuda-controller/v1','host':platform.node(),'pid':os.getpid(),
             'cwd':str(root),'command':command,'log':str(log),'status':'running',
             'started_utc':datetime.now(timezone.utc).isoformat(),'deadline_seconds':args.timeout,
             'next_check':'sweep.results.json / terminal.json within60seconds'}
    worker=None
    def stop(_signal,_frame):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM,stop);signal.signal(signal.SIGINT,stop)
    try:
        with log.open('w') as stream:
            worker=subprocess.Popen(command,cwd=root,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
            receipt.update(child_pid=worker.pid,child_pgid=worker.pid,
                           stop=f'ssh len kill -TERM {os.getpid()}')
            (output/'running.json').write_text(json.dumps(receipt,indent=2)+'\n')
            print(json.dumps(receipt),flush=True)
            try:
                code=worker.wait(timeout=args.timeout)
                receipt.update(status='completed' if code==0 else 'execution_error',returncode=code)
            except subprocess.TimeoutExpired:
                receipt.update(status='timeout',returncode=None)
    except KeyboardInterrupt:
        receipt.update(status='interrupted',returncode=None)
    except Exception as error:
        receipt.update(status='controller_error',error=repr(error),returncode=None)
    finally:
        if worker is not None:
            # Stop only the freshly created process group; retain all evidence.
            try:os.killpg(worker.pid,signal.SIGTERM)
            except ProcessLookupError:pass
            try:worker.wait(timeout=10)
            except subprocess.TimeoutExpired:
                try:os.killpg(worker.pid,signal.SIGKILL)
                except ProcessLookupError:pass
                worker.wait()
            try:os.killpg(worker.pid,0);group_exists=True
            except ProcessLookupError:group_exists=False
            receipt.update(child_reaped=worker.poll() is not None,process_group_exists=group_exists)
        receipt['elapsed_seconds']=time.monotonic()-started
        receipt['finished_utc']=datetime.now(timezone.utc).isoformat()
        terminal.write_text(json.dumps(receipt,indent=2)+'\n')
        print(json.dumps(receipt),flush=True)
    return 0 if receipt['status']=='completed' and not receipt.get('process_group_exists',False) else 1


if __name__=='__main__':raise SystemExit(main())
