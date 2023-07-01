// TODO(jdb): Rename `modules` to `capsules` in `ifrit_core`.
use anyhow::Result;
use async_trait::async_trait;

use ifrit_core::event_bus::{Event, EventKind};
use ifrit_core::module::{Module, ModuleCtx};

use ifrit_net::{get_interfaces, get_ip_address};

use aya::programs::KProbe;
use aya::Bpf;

/// An example recon module that monitors network traffic and emits events
/// to the event bus. The name of the module should be public, however any
/// internal state should be kept private. Any state that needs to be shared
/// between modules should be done through the event bus.
pub struct RipnetCapsule {
    pub name: String,
    ctx: ModuleCtx,
}

#[async_trait]
impl Module for RipnetCapsule {
    fn new(ctx: ModuleCtx) -> Self {
        RipnetCapsule {
            name: String::from("ripnet"),
            ctx,
        }
    }

    async fn run(&mut self) -> Result<()> {
        let mut interval = tokio::time::interval(tokio::time::Duration::from_secs(1));

        let interfaces = get_interfaces();
        let ips = &interfaces
            .iter()
            .map(|i| get_ip_address(i))
            .collect::<Vec<_>>();

        tracing::info!("Found ips {ips:?}");

        let mut bpf = Bpf::load_file("src/bpf/generic_file_open.bpf.o")?;

        // get the `kprobe` program compiled into `generic_file_open.o`.
        let program: &mut KProbe = bpf
            .program_mut("generic_file_open")
            .unwrap()
            .try_into()
            .unwrap();

        // load the program into the kernel
        program.load().unwrap();

        tracing::info!("Loaded generic file open bpf program");

        loop {
            tokio::select! {
                _ = interval.tick() => {

                    let event = Event {
                        // FIXME(jdb): Determine if we should make Event::module &'a str instead
                        // of String. This introduces a lifetime issue, but it would be nice to
                        // avoid the allocation.
                        module: self.name.to_string(),
                        inner: EventKind::StubEvent("Heartbeat".to_string()),
                    };
                    self.ctx.sender
                        .send(event)
                        .unwrap();
                },

            }
        }
    }
}
