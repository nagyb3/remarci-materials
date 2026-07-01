#include "door.h"

#include "signal.h"
#include "owen.h"
#include "magnetron.h"
#include "lamp.h"

void Door::open()
{
    _currentState = opened;
    _owen->_magn->send(Signal::open);
    _owen->_lamp->send(Signal::open);
}

void Door::close()
{
    _currentState = closed;
    _owen->_lamp->send(Signal::close);
}
