#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <mach-o/dyld.h>
#include <pthread.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <time.h>
#include <unistd.h>

static int logfd=-1;
static const char *roots=NULL;
static pthread_mutex_t lock=PTHREAD_MUTEX_INITIALIZER;
static __thread int busy=0;
static void quote(char *dst,size_t n,const char *s){size_t k=0;for(;*s&&k+3<n;s++){if(*s=='"'||*s=='\\')dst[k++]='\\';if((unsigned char)*s<32)dst[k++]='?';else dst[k++]=*s;}dst[k]=0;}
static void absolute(char *out,const char *path,int dirfd){
  if(path[0]=='/'){snprintf(out,4096,"%s",path);return;}
  char base[4096];
  if(dirfd==AT_FDCWD){if(!getcwd(base,sizeof base))base[0]=0;}
  else if(fcntl(dirfd,F_GETPATH,base)<0)base[0]=0;
  snprintf(out,4096,"%s/%s",base,path);
  // Canonicalize existing parents so a .. or symlink does not hide ownership.
  char parent[4096],real[4096];snprintf(parent,sizeof parent,"%s",out);
  char *slash=strrchr(parent,'/');if(slash){*slash=0;if(realpath(parent,real))snprintf(out,4096,"%s/%s",real,slash+1);}
}
static int owned(const char *path){if(!roots)return 0;for(const char *p=roots;*p;){const char *end=strchr(p,':');size_t n=end?(size_t)(end-p):strlen(p);if(n&&strncmp(path,p,n)==0&&(path[n]=='/'||path[n]==0))return 1;if(!end)break;p=end+1;}return 0;}
static void event(const char *kind,const char *op,const char *path,int blocked){
  if(logfd<0||busy)return;busy=1;
  char escaped[8192],line[8704];quote(escaped,sizeof escaped,path?path:"");
  struct timespec ts;clock_gettime(CLOCK_MONOTONIC,&ts);
  int len=snprintf(line,sizeof line,"{\"kind\":\"%s\",\"pid\":%d,\"time_ns\":%llu,\"op\":\"%s\",\"path\":\"%s\",\"blocked\":%s}\n",kind,getpid(),(unsigned long long)ts.tv_sec*1000000000ULL+ts.tv_nsec,op,escaped,blocked?"true":"false");
  pthread_mutex_lock(&lock);write(logfd,line,(size_t)len);pthread_mutex_unlock(&lock);busy=0;
}
static int mutation(const char *op,const char *path,int dirfd){if(busy)return 0;char abs[4096];absolute(abs,path,dirfd);int blocked=owned(abs);event("mutation",op,abs,blocked);if(blocked)errno=EACCES;return blocked;}
__attribute__((constructor)) static void init(void){
  roots=getenv("PROBE_IMMUTABLE_ROOTS");const char *p=getenv("PROBE_TRACE_LOG");
  if(p){int(*original)(const char*,int,...)=open;logfd=original(p,O_WRONLY|O_CREAT|O_APPEND,0600);}
  char exe[4096];uint32_t n=sizeof exe;if(_NSGetExecutablePath(exe,&n))snprintf(exe,sizeof exe,"unknown");event("load","process",exe,0);
}
#define INTERPOSE(repl,orig) __attribute__((used)) static struct {const void *r,*o;} ip_##orig __attribute__((section("__DATA,__interpose")))={(const void*)(uintptr_t)&repl,(const void*)(uintptr_t)&orig};
static int probe_open(const char *p,int flags,...){mode_t mode=0;if(flags&O_CREAT){va_list a;va_start(a,flags);mode=va_arg(a,int);va_end(a);}if((flags&(O_WRONLY|O_RDWR|O_CREAT|O_TRUNC|O_APPEND))&&mutation("open",p,AT_FDCWD))return -1;int(*fn)(const char*,int,...)=open;return fn(p,flags,mode);} INTERPOSE(probe_open,open)
static int probe_openat(int fd,const char *p,int flags,...){mode_t mode=0;if(flags&O_CREAT){va_list a;va_start(a,flags);mode=va_arg(a,int);va_end(a);}if((flags&(O_WRONLY|O_RDWR|O_CREAT|O_TRUNC|O_APPEND))&&mutation("openat",p,fd))return -1;int(*fn)(int,const char*,int,...)=openat;return fn(fd,p,flags,mode);} INTERPOSE(probe_openat,openat)
static FILE *probe_fopen(const char *p,const char *m){if((strchr(m,'w')||strchr(m,'a')||strchr(m,'+'))&&mutation("fopen",p,AT_FDCWD))return NULL;FILE *(*fn)(const char*,const char*)=fopen;return fn(p,m);} INTERPOSE(probe_fopen,fopen)
static int probe_mkdir(const char *p,mode_t m){if(mutation("mkdir",p,AT_FDCWD))return -1;int(*fn)(const char*,mode_t)=mkdir;return fn(p,m);} INTERPOSE(probe_mkdir,mkdir)
static int probe_unlink(const char *p){if(mutation("unlink",p,AT_FDCWD))return -1;int(*fn)(const char*)=unlink;return fn(p);} INTERPOSE(probe_unlink,unlink)
static int probe_rmdir(const char *p){if(mutation("rmdir",p,AT_FDCWD))return -1;int(*fn)(const char*)=rmdir;return fn(p);} INTERPOSE(probe_rmdir,rmdir)
static int probe_rename(const char *a,const char *b){if(mutation("rename-src",a,AT_FDCWD)||mutation("rename-dst",b,AT_FDCWD))return -1;int(*fn)(const char*,const char*)=rename;return fn(a,b);} INTERPOSE(probe_rename,rename)
static int probe_link(const char *a,const char *b){if(mutation("link-src",a,AT_FDCWD)||mutation("link-dst",b,AT_FDCWD))return -1;int(*fn)(const char*,const char*)=link;return fn(a,b);} INTERPOSE(probe_link,link)
static int probe_symlink(const char *a,const char *b){if(mutation("symlink",b,AT_FDCWD))return -1;int(*fn)(const char*,const char*)=symlink;return fn(a,b);} INTERPOSE(probe_symlink,symlink)
static int probe_chmod(const char *p,mode_t m){if(mutation("chmod",p,AT_FDCWD))return -1;int(*fn)(const char*,mode_t)=chmod;return fn(p,m);} INTERPOSE(probe_chmod,chmod)
static int probe_utimes(const char *p,const struct timeval t[2]){if(mutation("utimes",p,AT_FDCWD))return -1;int(*fn)(const char*,const struct timeval*)=utimes;return fn(p,t);} INTERPOSE(probe_utimes,utimes)
static int probe_connect(int fd,const struct sockaddr *a,socklen_t n){event("network","connect","",1);errno=EPERM;return -1;} INTERPOSE(probe_connect,connect)
// Cover libc entry points used by both Apple-SDK and Nix-built executables.
extern FILE *darwin_fopen(const char*,const char*) __asm("_fopen$DARWIN_EXTSN");
extern int nocancel_open(const char*,int,...) __asm("_open$NOCANCEL");
extern int nocancel_openat(int,const char*,int,...) __asm("_openat$NOCANCEL");
INTERPOSE(probe_fopen,darwin_fopen)
INTERPOSE(probe_open,nocancel_open)
INTERPOSE(probe_openat,nocancel_openat)
