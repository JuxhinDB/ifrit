use anyhow::Result;
use tokio::sync::broadcast;

#[derive(Clone, Debug)]
pub struct Event {
    pub module: String,
    pub inner: EventKind,
}

#[derive(Clone, Debug)]
pub enum EventKind {
    // Temporary stub event to send arbitrary strings between
    // modules for testing purposes.
    StubEvent(String),
}

#[derive(Debug)]
pub struct EventBus {
    pub sender: broadcast::Sender<Event>,
    pub receiver: broadcast::Receiver<Event>,
}

impl Clone for EventBus {
    fn clone(&self) -> Self {
        Self {
            sender: self.sender.clone(),
            receiver: self.sender.subscribe(),
        }
    }
}

impl Default for EventBus {
    fn default() -> Self {
        Self::new()
    }
}

impl EventBus {
    // fn new() -> Self
    // fn register_module(&mut self, id: ModuleID, module: Box<dyn Module>)
    // fn unregister_module(&mut self, id: ModuleID)
    // fn send_event(&self, event: Event)
    // fn process_events(&mut self)
    pub fn new() -> Self {
        let (sender, receiver) = broadcast::channel(100);
        EventBus { sender, receiver }
    }

    pub async fn send(&self, event: Event) -> Result<()> {
        self.sender.send(event)?;
        Ok(())
    }

    pub fn subscribe(&self) -> broadcast::Receiver<Event> {
        self.sender.subscribe()
    }
}
