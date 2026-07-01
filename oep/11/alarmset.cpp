#include "alarmset.h"

#include "signal.h"
#include "system.h"

void AlarmSet::transition(Signal sig)
{
    switch(_currentState){
        case passive:
            switch (sig){
                case on:       if (_sys->allDoorsClosed()) { _currentState = active; } break;
                case off:      break;
                case open:     break;
                case movement: break;
                default: assert(false);
            }
            break;
        case active:
            switch (sig){
                case on:       break;
                case off:      _currentState = passive; break;
                case open:     _currentState = alarm; break;
                case movement: _currentState = alarm; break;
                default: assert(false);
            }
            break;
        case alarm:
            switch (sig){
                case on:       break;
                case off:      _currentState = passive; break;
                case open:     break;
                case movement: break;
                default: assert(false);
            }
            break;
        default: assert(false);
    }
}