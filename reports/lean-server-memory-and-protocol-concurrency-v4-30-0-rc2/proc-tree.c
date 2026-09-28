#include <libproc.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static pid_t seen[4096]; static size_t nseen=0; static uint64_t total=0;
static int has_seen(pid_t p){for(size_t i=0;i<nseen;i++)if(seen[i]==p)return 1;return 0;}
static void visit(pid_t pid,int depth){
 if(depth>64||nseen>=4096||has_seen(pid))return;
 seen[nseen++]=pid;
 struct proc_taskinfo info; memset(&info,0,sizeof(info));
 int n=proc_pidinfo(pid,PROC_PIDTASKINFO,0,&info,sizeof(info));
 char name[PROC_PIDPATHINFO_MAXSIZE]={0};proc_name(pid,name,sizeof(name));
 if(n==(int)sizeof(info)){printf("%d\t%s\t%llu\n",pid,name,(unsigned long long)info.pti_resident_size);total+=info.pti_resident_size;}
 pid_t children[2048]; int bytes=proc_listchildpids(pid,children,sizeof(children));
 if(bytes>0){size_t count=(size_t)bytes/sizeof(pid_t);if(count>2048)count=2048;for(size_t i=0;i<count;i++)visit(children[i],depth+1);}
}
int main(int argc,char **argv){if(argc!=2)return 2;visit((pid_t)strtol(argv[1],0,10),0);printf("TOTAL\t%llu\n",(unsigned long long)total);return 0;}
