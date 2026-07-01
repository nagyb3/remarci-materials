#pragma once

#include "signal.h"
#include "statemachine.hpp"

#include <string>
#include <cassert>

class Owen;

enum MagnetronState { working, out_of_work };

class Magnetron : public StateMachine<Signal, MagnetronState>
{
public:
    Owen* _owen;

    Magnetron(Owen* o) : StateMachine<Signal, MagnetronState>(), _owen(o){}
    ~Magnetron(){ finalstep(); }

    std::string writeState(){
        switch (_currentState) {
            case working     : return "working";
            case out_of_work : return "out of working";
            default          : assert(false);
        }
    }
private:
    void initState() override;
    void transition(Signal sig) override;

};
