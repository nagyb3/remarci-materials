#pragma once

#include "signal.h"

#include "signal.h"
#include "statemachine.hpp"

#include <string>
#include <cassert>

class Owen;

enum LampState { lit, not_lit };

class Lamp : public StateMachine<Signal, LampState>
{
public:
    Owen* _owen;

    Lamp(Owen* o) : StateMachine<Signal, LampState>(), _owen(o){}
    ~Lamp() { finalstep(); }

    std::string writeState(){
        switch (_currentState) {
            case lit     : return "lit";
            case not_lit : return "not lit";
            default      : assert(false);
        }
    }
private:
    void initState() override;
    void transition(Signal sig) override;
};
