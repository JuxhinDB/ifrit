use anyhow::Result;
use std::net::IpAddr;

use pnet::datalink::Channel::Ethernet;
use pnet::datalink::{self, NetworkInterface};
use pnet::ipnetwork::IpNetwork;
use pnet::packet::{MutablePacket, Packet};

use pnet::packet::ethernet::{EthernetPacket, MutableEthernetPacket};

/// Returns the network interface for the device.
pub fn get_interfaces() -> Vec<NetworkInterface> {
    datalink::interfaces()
}

/// Returns the MAC address of the network interface.
pub fn get_mac_address(interface: &NetworkInterface) -> [u8; 6] {
    interface.mac.unwrap().octets()
}

/// Returns the IP address of the network interface.
pub fn get_ip_address(interface: &NetworkInterface) -> IpAddr {
    interface.ips[0].ip()
}

/// Get the default gateway for the network interface using `iproute2`.
pub fn get_default_gateway(interface: &NetworkInterface) -> Vec<IpNetwork> {
    interface.ips.clone()
}

pub fn connect_to_interface(
    interface: &NetworkInterface,
) -> Result<(
    Box<dyn datalink::DataLinkSender>,
    Box<dyn datalink::DataLinkReceiver>,
)> {
    match datalink::channel(&interface, Default::default()) {
        Ok(Ethernet(tx, rx)) => return Ok((tx, rx)),
        Ok(_) => anyhow::bail!("Unhandled channel type"),
        Err(e) => anyhow::bail!(
            "An error occurred when creating the datalink channel: {}",
            e
        ),
    }
}
