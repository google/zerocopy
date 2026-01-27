#![allow(dead_code)]

use crate::MacAddressError;
use nix::ifaddrs::*;

/// Uses the `getifaddrs` call to retrieve a list of network interfaces on the
/// host device and returns the first MAC address listed that isn't
/// local-loopback or if a name was specified, that name.
pub fn get_mac(name: Option<&str>) -> Result<Option<[u8; 6]>, MacAddressError> {
    let ifiter = getifaddrs()?;

    for interface in ifiter {
        if let Some(iface_address) = interface.address {
            if let Some(link) = iface_address.as_link_addr() {
                let bytes = link.addr();

                if let Some(name) = name {
                    if interface.interface_name == name {
                        return Ok(bytes);
                    }
                } else if let Some(bytes) = bytes {
                    if bytes.iter().any(|&x| x != 0) {
                        return Ok(Some(bytes));
                    }
                }
            }
        }
    }

    Ok(None)
}

pub fn get_ifname(mac: &[u8; 6]) -> Result<Option<String>, MacAddressError> {
    let ifiter = getifaddrs()?;

    for interface in ifiter {
        if let Some(iface_address) = interface.address {
            if let Some(link) = iface_address.as_link_addr() {
                let bytes = link.addr();

                if bytes == Some(*mac) {
                    return Ok(Some(interface.interface_name));
                }
            }
        }
    }

    Ok(None)
}
