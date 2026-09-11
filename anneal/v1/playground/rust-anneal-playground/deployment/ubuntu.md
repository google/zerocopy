### Amazon EC2 (Ubuntu)

Here's an example session. This could definitely be improved and
automated.

#### Dependencies (as root)

```
apt-get update
apt-get upgrade -y
apt-get install git awscli nginx

# Install Docker CE
# Configure apt-get per instructions
# https://docs.docker.com/engine/installation/linux/docker-ce/ubuntu/
apt-get install docker-ce

# Use a production-quality storage driver that doesn't leak disk space
cat >>/etc/docker/daemon.json <<EOF
{
    "storage-driver": "overlay2"
}
EOF

# Ensure Docker can control the PID limit
mount | grep cgroup/pids

# Ensure Docker can control swap limit
# https://docs.docker.com/engine/installation/linux/linux-postinstall/#your-kernel-does-not-support-cgroup-swap-limit-capabilities

service docker restart
usermod -a -G docker ubuntu # user needs to log out and in again

fallocate -l 1G /swap.fs
chmod 0600 /swap.fs
mkswap /swap.fs
```

#### Set aside disk space (as root)
```
fallocate -l 512M /playground.fs
device=$(losetup -f --show /playground.fs)
mkfs -t ext3 -m 1 -v $device
mkdir /mnt/playground
```

#### Configure disk mountpoints (as root)
```
cat >>/etc/fstab <<EOF
/swap.fs        none            swap   sw       0   0
/playground.fs /mnt/playground  ext3   loop     0   0
EOF
```

Reboot the instance at this point.

#### Get the code
```
git clone https://github.com/rust-lang/rust-playground.git
cd rust-playground
```

#### Set a crontab to update the assets, binary, and docker containers

```
crontab -e
```

Review the [example crontab](crontab) in this repo. It calls [`update.sh`](update.sh) also in this repo.

#### Install the SystemD service

[playground.service](playground.service)

```
cp playground.service /etc/systemd/system/playground.service
service playground start
systemctl enable playground.service
```

#### Install the Nginx reverse proxy

[playground-reverse-proxy](playground-reverse-proxy)

```
cp playground-reverse-proxy /etc/nginx/sites-enabled
service nginx reload
```

#### Configure SSL
