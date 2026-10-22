#!/usr/bin/env python3
"""Compile the exact archived Phase 6 Lean source closure, then Chapter7Phase6Native."""
import base64, hashlib, os, pathlib, re, subprocess, sys, zipfile

root=pathlib.Path(__file__).resolve().parents[1]
work=root/'.chapter7-build'
work.mkdir(exist_ok=True)
encoded=(root/'.chapter7-sources/phase6-pinned-closure.b64').read_text().strip()
archive=base64.b64decode(encoded,validate=True)
expected='b573bf428c3df531f242a2c32c154cbe056b0b3dc9a7731f9645f6d3eb4f992b'
actual=hashlib.sha256(archive).hexdigest()
if actual!=expected:
  raise RuntimeError('The source closure checksum differs: '+actual)
zip_path=work/'phase6-source.zip'
zip_path.write_bytes(archive)
src=work/'original-phase6'
with zipfile.ZipFile(zip_path) as z:
  for item in z.infolist():
    rel=pathlib.PurePosixPath(item.filename)
    if rel.is_absolute() or '..' in rel.parts:
      raise RuntimeError('Unsafe ZIP entry '+item.filename)
  z.extractall(src)
files={p.stem:p for p in src.rglob('*.lean')}
assert len(files)==103,(len(files),sorted(files)[:20])
candidates=['Chapter7Phase6Native','Phase6Godel','Phase6Kernel']
main_file=root/'B5Foundation/Chapter7Phase6Native.lean'
files['Chapter7Phase6Native']=main_file
rx=re.compile(r'^\s*(?:public\s+)?import\s+([\w.]+)',re.M)
order=[];visiting=set();done=set()
def visit(name):
  if name in done or name not in files:
    return
  if name in visiting:
    raise RuntimeError('Import cycle: '+name)
  visiting.add(name)
  for imported in rx.findall(files[name].read_text()):
    visit(imported)
  visiting.remove(name)
  done.add(name)
  order.append(name)
for entry in candidates:
  visit(entry)
print('Verified pinned original source:',actual, 'declared Lean sources:',len(files),
      'reachable modules to compile:',len(order), flush=True)
oleans=work/'oleans'
oleans.mkdir(exist_ok=True)
base_lean_path=subprocess.check_output(['lake','env','bash','-c','printf %s "$LEAN_PATH"'],
       cwd=root/'B5Foundation',text=True).strip()
if not base_lean_path:
  raise RuntimeError('lake supplied empty LEAN_PATH')
env=os.environ.copy()
env['LEAN_PATH']=str(oleans)+os.pathsep+base_lean_path
env['LEAN_NUM_THREADS']='1'
print('Original source modules:',len(order)-1, flush=True)
for i,name in enumerate(order,1):
  out=oleans/(name+'.olean')
  cmd=['lake','env','lean','-o',str(out),str(files[name].resolve())]
  proc=subprocess.run(cmd,cwd=root/'B5Foundation',env=env,stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,text=True)
  print(f'[{i}/{len(order)}] {name}: {proc.returncode}',flush=True)
  if proc.stdout:
    print(proc.stdout[-18000:],flush=True)
  if proc.returncode:
    raise SystemExit(f'Lean failed compiling {name}; no certificate issued')
  if name=='Chapter7Phase6Native':
    ax=proc.stdout
    if 'sorryAx' in ax or 'error:' in ax:
      raise RuntimeError('Unacceptable proof dependency or Lean error')
print('CHAPTER7_PHASE6_CANONICAL_ALL12_KERNEL_SUCCESS',flush=True)
