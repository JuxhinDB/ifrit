# Capsules

Capsules are specialised modules that can be loaded into the main Ifrit runtime
during startup. They can have specific use-cases such as:

* Perform network analysis and exploits
* Handling hardware interrupts
* Updating any UI state

They may also be auxiliary capsules such as:

* Logging
* Stats & metrics
* External telemetry and diagnostics

They rely on the entire `ifrit-*` ecosystem in order to power each capsule.

#### Why "capsule"

No particular reason besides sounding cool. I wanted something that felt like a
piece of sci-fi being loaded into large system to augment its abilities.
