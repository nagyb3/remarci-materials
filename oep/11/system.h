#pragma once

#include "alarmset.h"
#include "door.h"

#include <vector>
#include <sstream>
#include <iostream>

class System
{
public:
    System(int n)
    {
        _doors.reserve(n);
        for (int i = 0; i < n; ++i) {
            _doors.push_back(new Door(this));
        }
        _alarm = new AlarmSet(this);
    }
    ~System()
    {
        delete _alarm;
        for (int i = 0; i < _doors.size(); ++i) {
            delete _doors[i];
        }
    }

    bool allDoorsClosed() const {
        for (const auto& e : _doors){
            if (!e->isClosed()) {
                return false;
            }
        }
        return true;
    }

    AlarmSet* _alarm;
    std::vector<Door*> _doors;

    void writeState()
    {
        std::this_thread::sleep_for(std::chrono::milliseconds(100));
        std::ostringstream out;
        out << "   States:\n";
        if (allDoorsClosed()) out << "      all doors are closed\n";
        else  out << "      at least one door is open\n";
        out << "      alarm is "     << _alarm->writeState() << std::endl << std::endl;
        std::cout << out.str();
    }
};
