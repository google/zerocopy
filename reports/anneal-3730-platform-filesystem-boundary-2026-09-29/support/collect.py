#!/usr/bin/env python3
"""Read-only runtime inventory plus two bounded scratch-only filesystem probes."""
import hashlib, json, os, platform, pwd, shutil, subprocess
from pathlib import Path

HERE=Path(__file__).resolve().parent
SCRATCH=Path(os.environ['ANNEAL_PROBE_SCRATCH']).resolve()
SCRIPT=HERE/'fs_probe.pl'
OUT=HERE/'results.json'
RUNTIMES=['docker','podman','colima','limactl','lima','nerdctl','container',
          'qemu-system-aarch64','qemu-system-x86_64','multipass','orbctl','perl']

def call(name, argv, input_text=None, env=None, timeout=30):
    p=subprocess.run(argv,input=input_text,text=True,capture_output=True,
                     env=env,timeout=timeout)
    return {'name':name,'argv':[str(x).replace(str(SCRATCH),'$SCRATCH').replace(str(SCRIPT),'$PROBE') for x in argv],
            'rc':p.returncode,'stdout':p.stdout.replace(str(SCRATCH),'$SCRATCH'),
            'stderr':p.stderr.replace(str(SCRATCH),'$SCRATCH')}

def parse_probe(r):
    if r['rc']!=0:raise RuntimeError(r)
    lines=r['stdout'].splitlines()
    values={}
    for line in lines:
        key,value=line.split('\t',1)
        values[key]=value
    assert values['replace_old_fd']=='OLD_GENERATION'
    assert values['replace_new_path']=='NEW_GENERATION'
    assert values['unlink_open_fd']=='NEW_GENERATION'
    assert values['unlink_path_missing']=='1'
    assert values['flock_child_while_held']=='0'
    assert values['flock_child_after_release']=='1'
    assert values['sampled_invalid_reads']=='0'
    assert values['sampled_missing_reads']=='0'
    assert int(values['sampled_old_reads'])>0 and int(values['sampled_new_reads'])>0
    assert values['cleanup_complete']=='1'
    return values

def main():
    assert SCRATCH.is_dir() and SCRIPT.is_file()
    inv={'host_platform':platform.platform(),
         'host_uname':call('host_uname',['uname','-srm']),
         'sw_vers':call('sw_vers',['sw_vers']),
         'runtime_paths':{name:shutil.which(name) for name in RUNTIMES},
         'scratch_df':call('scratch_df',['df','-h',str(SCRATCH)]),
         'data_volume':call('data_volume',['diskutil','info','/System/Volumes/Data']),
         'docker_info':call('docker_info',['docker','info','--format',
                'OSType={{.OSType}} Architecture={{.Architecture}} Driver={{.Driver}} Kernel={{.KernelVersion}} DockerRootDir={{.DockerRootDir}}']),
         'orbctl_list':call('orbctl_list',['orbctl','list'],
                env=dict(os.environ,HOME=pwd.getpwuid(os.getuid()).pw_dir)),
         'cached_images':call('cached_images',['docker','image','ls','--format',
                '{{.ID}} {{.Repository}}:{{.Tag}} {{.Size}}']),
         'ubuntu_image':call('ubuntu_image',['docker','image','inspect','--platform','linux/amd64',
                'ubuntu:24.04','--format','Id={{.Id}} Os={{.Os}} Arch={{.Architecture}} Size={{.Size}} RepoDigests={{json .RepoDigests}}'])}
    # Diskutil includes unrelated local snapshot metadata; retain only volume identity.
    raw_volume=inv['data_volume']['stdout']
    inv['data_volume']['raw_stdout_sha256']=hashlib.sha256(raw_volume.encode()).hexdigest()
    wanted=('Device Identifier:', 'Volume Name:', 'Mount Point:',
            'File System Personality:', 'Type (Bundle):', 'Protocol:', 'APFS Container:')
    inv['data_volume']['stdout']='\n'.join(line for line in raw_volume.splitlines()
        if line.strip().startswith(wanted))+'\n'
    assert all(inv[k]['rc']==0 for k in ('host_uname','sw_vers','scratch_df','data_volume','docker_info','orbctl_list','cached_images','ubuntu_image'))
    assert 'APFS' in inv['data_volume']['stdout']
    assert 'ubuntu:24.04' in inv['cached_images']['stdout']
    linux_command=['docker','run','--pull=never','--platform=linux/amd64','--network=none',
                   '--rm','-i','ubuntu:24.04','sh','-c',
                   'uname -srm; cat /etc/os-release | head -4; stat -f -c "filesystem=%T" /tmp']
    inv['linux_runtime']=call('linux_runtime',linux_command,timeout=30)
    assert inv['linux_runtime']['rc']==0 and 'filesystem=overlayfs' in inv['linux_runtime']['stdout']
    results={'inventory':inv,'probes':[]}
    for i in (1,2):
        host=call('host_apfs_run'+str(i),['perl',str(SCRIPT)],
                  env=dict(os.environ,PROBE_ROOT=str(SCRATCH)),timeout=30)
        container=call('linux_overlayfs_run'+str(i),
            ['docker','run','--pull=never','--platform=linux/amd64','--network=none','--rm','-i',
             '-e','PROBE_ROOT=/tmp','ubuntu:24.04','perl','-'],
            input_text=SCRIPT.read_text(),timeout=30)
        results['probes'].append({'host':host,'host_values':parse_probe(host),
                                  'container':container,'container_values':parse_probe(container)})
    OUT.write_text(json.dumps(results,indent=2,ensure_ascii=False)+'\n')
    print('host/container trials:',len(results['probes']))
    for i,r in enumerate(results['probes'],1):
        print(i,'host',r['host_values']['sampled_old_reads'],r['host_values']['sampled_new_reads'],
              'container',r['container_values']['sampled_old_reads'],r['container_values']['sampled_new_reads'])

if __name__=='__main__':main()
