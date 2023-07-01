//! Module handling the interfaces and traits for all other modules
//! utilised by Ifrit. This is particularly important to standardise
//! behaviour across modules, and to allow for easy addition of new
//! modules.
//!
//! All modules are designed to subscribe and publish events to the
//! event bus -- allowing for easy communication between modules.
//!
//! For the time being modules are rudimentary. They have hard-coded
//! configurations and two states: running and stopped. In the future
//! modules will be able to be configured and will have more states
//! (e.g. paused, etc.).
//!
//! Module management is also rudimentary. This is so separate event bus
//! and the module manager is simply another module that interacts over
//! the same event bus.
use anyhow::Result;
use async_trait::async_trait;
use tokio::sync::broadcast;

use crate::event_bus::{Event, EventBus};

#[async_trait]
pub trait Module {
    fn new(ctx: ModuleCtx) -> Self;
    async fn run(&mut self) -> Result<()>;
}

#[derive(Debug)]
pub struct ModuleCtx {
    pub sender: broadcast::Sender<Event>,
    pub receiver: broadcast::Receiver<Event>,
}

impl ModuleCtx {
    pub fn new(bus: &EventBus) -> Self {
        let sender = bus.sender.clone();
        let receiver = bus.subscribe();

        ModuleCtx { sender, receiver }
    }
}
