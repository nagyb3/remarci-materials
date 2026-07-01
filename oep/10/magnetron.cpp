#include "magnetron.h"

#include "signal.h"
#include "owen.h"

#include <iostream>

void Magnetron::initState()
{
    _currentState = out_of_work;
}

void Magnetron::transition(Signal sig)
{
    switch(_currentState){
        case working:
            switch (sig){
                case press: _currentState = out_of_work;
                            _owen->_lamp->send(Signal::stop);
                            break;
                case open:  _currentState = out_of_work; break;
                default: assert(false);
            }
            break;
        case out_of_work:
            switch (sig){
                case press:
                    if( _owen->_door->_currentState == Door::closed ) {
                        _currentState = working;
                        _owen->_lamp->send(Signal::start);
                    }
                    break;
                case open: break;
                default: assert(false);
            }
            break;
        default: assert(false);
    }
}
