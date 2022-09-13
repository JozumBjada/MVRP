# MVRP
Automated generation of optical-element sequences based on the proposal in [Phys. Rev. Lett. 116, 090405 (2016)](https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.116.090405).

The goal is to generate a quantum pure state whose form conforms to given constraints, where SPDC (spontaneous parametric down-conversion) sources are used to generate a physical system (biphotons) and given optical elements are used to manipulate the system. The result is a sequence of actions that transform the system from its initial state to the desired state.

**analyzeSetups.nb** - user interface

**mvrp.wl** - processing routines, especially `runSearch` that searches for a sequence of elements generating the desired state

**mvrp_visualization.wl** - visualization tools, especially `visualizeSetup` and `analyzeSetup`

**test_file.txt** - test file that stores one result of an (unsuccessful) search
