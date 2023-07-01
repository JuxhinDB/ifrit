// TODO(jdb): Rename modules to capsules in `ifrit_core`.
use anyhow::Result;
use async_trait::async_trait;
use ifrit_core::event_bus::EventKind;
use ifrit_core::module::{Module, ModuleCtx};

/// An example recon module that monitors network traffic and emits events
/// to the event bus. The name of the module should be public, however any
/// internal state should be kept private. Any state that needs to be shared
/// between modules should be done through the event bus.
pub struct LoggerCapsule {
    pub name: String,
    ctx: ModuleCtx,
}

#[async_trait]
impl Module for LoggerCapsule {
    fn new(ctx: ModuleCtx) -> Self {
        LoggerCapsule {
            name: String::from("logger"),
            ctx,
        }
    }

    async fn run(&mut self) -> Result<()> {
        loop {
            tokio::select! {
                e = self.ctx.receiver.recv() => {
                    match e {
                        Ok(event) => {
                            match event.inner {
                                EventKind::StubEvent(message) => tracing::info!("{}: received event: {}", &self.name, message),
                            }
                        },
                        Err(e) => println!("Error: {}", e),
                    }
                },
            }
        }
    }
}
