#pragma once

#include "button.h"
#include "door.h"
#include "lamp.h"
#include "magnetron.h"

#include <iostream>
#include <sstream>

class Owen
{
public:
    Button* _button;
    Magnetron* _magn;
    Lamp* _lamp;
    Door* _door;

    Owen()
    {
        _button = new Button(this);
        _magn = new Magnetron(this);
        _lamp = new Lamp(this);
        _door = new Door(this);
    }
    ~Owen()
    {
        delete _button;
        delete _magn;
        delete _lamp;
        delete _door;
    }

    void writeState()
    {
        std::this_thread::sleep_for(std::chrono::milliseconds(50));
        std::ostringstream out;
        out << "   States:\n";
        out << "      door is "      << _door->writeState() << std::endl;
        out << "      lamp is "      << _lamp->writeState() << std::endl;
        out << "      magnetron is " << _magn->writeState() << std::endl << std::endl;
        std::cout << out.str();
    }
};
