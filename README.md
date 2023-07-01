> **Note**
> This project is still a work-in-progress.

---

# Ifrit

Ifrit is a modular, event-driven networking tool aimed at performing fun and educational WiFi hacking tasks. It is designed to be powered by a Raspberry Pi 0 or similar devices.

## Features

* Modular design, with each module targeting a specific network exploit, remaining alive indefinitely or until turned off.
* Event-driven system where modules communicate through a shared event bus.
* Auxiliary modules for functionalities like driving an LCD display, performing logging, etc.
* Strong control over parsing packets and sending arbitrary network packets using the `libpnet` library.

## Architecture

The project is structured around the central binary `ifrit` that interfaces with other crates exposing libraries. For example, network packet handling resides in an `ifrit-net` package, which is internally powered by `libpnet`.

## Formal Verification

We use TLA+ to model and verify the system's behavior. The specifications reside in the `spec` directory. To learn more about our formal verification process, please read the [spec README](spec/README.md).
