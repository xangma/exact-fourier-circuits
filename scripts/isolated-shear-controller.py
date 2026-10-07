#!/usr/bin/env python3
"""Run the isolated shear diagnostic with a deadline and retained exit state."""
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

root=Path(__file__).resolve().parents[1]
output=root/'output';output.mkdir(exist_ok=True)
command=[sys.executable,'-I','-u',str(root/'scripts/check-isolated-shear.py'),'--output',str(output)]
receipt={'host':'len','cwd':str(root),'pid':os.getpid(),'command':command,
         'log':str(output/'run.log'),'deadline_seconds':180,
         'stop':f'ssh len kill -TERM {os.getpid()}','status':'running'}
started=time.monotonic();worker=None
def interrupted(signum,frame):raise KeyboardInterrupt
signal.signal(signal.SIGTERM,interrupted);signal.signal(signal.SIGINT,interrupted)
try:
    with (output/'run.log').open('w') as stream:
        worker=subprocess.Popen(command,cwd=root,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
        receipt['worker_pid']=worker.pid
        (output/'running.json').write_text(json.dumps(receipt,indent=2)+'\n')
        print(json.dumps(receipt),flush=True)
        try:
            code=worker.wait(timeout=180)
            receipt.update(status='completed' if code==0 else 'execution_error',returncode=code)
        except subprocess.TimeoutExpired:receipt.update(status='timeout',returncode=None)
except KeyboardInterrupt:receipt.update(status='interrupted',returncode=None)
except Exception as exc:receipt.update(status='controller_error',error=repr(exc))
finally:
    if worker is not None:
        try:os.killpg(worker.pid,signal.SIGTERM)
        except ProcessLookupError:pass
        try:worker.wait(timeout=10)
        except subprocess.TimeoutExpired:
            try:os.killpg(worker.pid,signal.SIGKILL)
            except ProcessLookupError:pass
            worker.wait()
        try:os.killpg(worker.pid,0);remains=True
        except ProcessLookupError:remains=False
        receipt.update(child_reaped=worker.poll() is not None,worker_group_exists=remains)
    receipt['elapsed_seconds']=time.monotonic()-started
    (output/'terminal.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt),flush=True)
sys.exit(0 if receipt['status']=='completed' and not receipt.get('worker_group_exists',False) else 1)
