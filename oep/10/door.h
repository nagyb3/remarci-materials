#pragma once

#include <string>
#include <cassert>

class Owen;

class Door
{
public:
    enum State { opened, closed };
    State _currentState;
    Owen* _owen;

    Door(Owen* o) : _currentState(closed), _owen(o) {}
    void open()  ;
    void close() ;

    std::string writeState(){
        switch (_currentState) {
            case opened : return "opened";
            case closed : return "closed";
            default     : assert(false);
        }
    }
};