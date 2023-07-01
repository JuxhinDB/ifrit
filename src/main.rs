#[macro_use]
extern crate tcprint;

use anyhow::Result;
use tcprint::{BasicColors, ColorPrintState};
use tracing_subscriber::prelude::*;

use ifrit_core::{
    event_bus::{EventBus, EventKind},
    module::{Module, ModuleCtx},
};

use logger::LoggerCapsule;
use ripnet::RipnetCapsule;

#[tokio::main]
async fn main() -> Result<()> {
    // Initialize the tracing subscriber globally
    // FIXME(jdb): Place this behind debug_assertions flag
    let console_layer = console_subscriber::spawn();

    let tracing_layer = tracing_subscriber::fmt::layer()
        .with_level(true)
        .with_ansi(true)
        .with_timer(tracing_subscriber::fmt::time::SystemTime)
        .with_filter(tracing_subscriber::EnvFilter::from_default_env());

    tracing_subscriber::registry()
        .with(console_layer)
        .with(tracing_layer)
        .init();

    // Initialize the Tokio console subscriber when running in debug mode

    let mut state = ColorPrintState::<BasicColors>::default();

    tcprintln!(
        state,
        [
            red:
            r#"
 ██▓  █████▒██▀███   ██▓▄▄▄█████▓
▓██▒▓██   ▒▓██ ▒ ██▒▓██▒▓  ██▒ ▓▒
▒██▒▒████ ░▓██ ░▄█ ▒▒██▒▒ ▓██░ ▒░
░██░░▓█▒  ░▒██▀▀█▄  ░██░░ ▓██▓ ░ 
░██░░▒█░   ░██▓ ▒██▒░██░  ▒██▒ ░ 
░▓   ▒ ░   ░ ▒▓ ░▒▓░░▓    ▒ ░░   
 ▒ ░ ░       ░▒ ░ ▒░ ▒ ░    ░    
 ▒ ░ ░ ░     ░░   ░  ▒ ░  ░      
 ░            ░      ░           
    "#
        ]
    );

    // Create a new EventBus
    let event_bus = EventBus::new();

    // Clone the EventBus for each module/task
    let ripnet_ctx = ModuleCtx::new(&event_bus);
    let mut ripnet = RipnetCapsule::new(ripnet_ctx);

    let logger_ctx = ModuleCtx::new(&event_bus);
    let mut logger = LoggerCapsule::new(logger_ctx);

    tokio::join!(ripnet.run(), logger.run()).0?;

    // The issue here is that the while loop at the end of your main function,
    // which waits for and processes events, will run forever because
    // receiver.recv().await will never return Err as long as the sender side
    // of the channel is not dropped.
    //
    // Since you've cloned the sender and moved the clones into the tokio
    // tasks, even though you wait for those tasks to finish, the original
    // sender in the main thread still exists, so the receivertr will keep
    // waiting for more events that will never come.
    drop(event_bus.sender);

    // Process the events
    let mut receiver = event_bus.receiver;

    while let Ok(event) = receiver.recv().await {
        match event.inner {
            EventKind::StubEvent(message) => println!("Received event: {}", message),
        }
    }

    Ok(())
}
