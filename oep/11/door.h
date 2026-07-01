#pragma once

#include "signal.h"
#include "statemachine.hpp"
#include <cassert>

class System;

enum DoorState { closed, opened };

class Door : public StateMachine<Signal, DoorState>
{
public:
    System* _sys;

    Door(System *s) : StateMachine<Signal, DoorState>(), _sys(s){}
    ~Door() { finalstep(); }

    std::string writeState(){
        switch (_currentState) {
            case closed : return "closed";
            case opened : return "opened";
            default     : assert(false);
        }
    }

    bool isClosed() { return _currentState == closed; }

private:
    void transition(Signal sig) override;
    void initState() override { _currentState = closed; }
};
