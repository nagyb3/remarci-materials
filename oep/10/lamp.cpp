#include "lamp.h"

#include "signal.h"
#include "owen.h"

void Lamp::initState()
{
    _currentState = not_lit;
}

void Lamp::transition(Signal sig)
{
    switch (_currentState){
        case lit:
            switch (sig){
                case start: break;
                case open: break;
                case stop: 
                case close: _currentState = not_lit; break;
                default: assert(false);
            }
            break;
        case not_lit:
            switch (sig){
                case start: 
                case open:  _currentState = lit; break;
                case stop:  break;
                case close: break;
                default: assert(false);
            }
            break;
        default: assert(false);
    }
}


