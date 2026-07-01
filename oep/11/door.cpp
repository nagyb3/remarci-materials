#include "door.h"

#include "signal.h"
#include "system.h"

void Door::transition(Signal sig)
{
    switch(_currentState){
        case closed:
            switch (sig){
                case open:  _currentState = opened; break;
                case close: break;
                default: assert(false);
            }
            break;
        case opened:
            switch (sig){
                case open:  break;
                case close: _currentState = closed; break;
                default: assert(false);
            }
            break;
        default: assert(false);
    }
}
