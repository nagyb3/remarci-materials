#include "button.h"
#include "owen.h"
#include "magnetron.h"
#include "signal.h"

void Button::press() const{
    _owen->_magn->send(Signal::press);
}