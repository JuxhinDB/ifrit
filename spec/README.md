# Ifrit Specifications
This directory contains formal specifications for the behavior of the Ifrit system, written in TLA+.

## Overview
The Ifrit system is designed to be a modular, event-driven system for network exploration and exploitation. Each module in the system can perform a specific task, such as ARP Spoofing or managing an LCD display. Modules communicate with each other through a shared event bus.

The specifications in this directory model the behavior of the Ifrit system at a high level. They are intended to help ensure that the system behaves as expected, and to serve as a form of documentation that is precise and unambiguous.

## Specifications

* `ModuleLifecycle.tla` - This specification describes the lifecycle of a module in the Ifrit system. It models the possible states a module can be in, and the transitions between those states.

* `EventBus.tla` - This specification models the behavior of the event bus. It includes the broadcasting of events to all modules, and the handling of events by modules.

## Checking the Specifications
To check these specifications, you can use the TLA+ Toolbox, a comprehensive IDE for TLA+. For each specification, the [TLA+ Toolbox](https://lamport.azurewebsites.net/tla/toolbox.html) can check that the behavior described in the specification is consistent and satisfies any invariants or properties defined in the specification.

