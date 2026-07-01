#pragma once

#include "signal.h"
#include "statemachine.hpp"

#include <string>
#include <cassert>

class System;

enum AlarmState { passive, active, alarm };

class AlarmSet : public StateMachine<Signal, AlarmState>
{
public:
    System* _sys;

    AlarmSet(System *s) : StateMachine<Signal, AlarmState>(), _sys(s){}
    ~AlarmSet() { finalstep(); }

    std::string writeState(){
        switch (_currentState) {
            case passive: return "passive";
            case active : return "active";
            case alarm  : return "BEEP BEEP BEEP";
            default     : assert(false);
        }
    }

private:
    void transition(Signal sig) override;
    void initState() override { _currentState = passive; }
};