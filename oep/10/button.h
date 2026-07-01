#pragma once

class Owen;

class Button
{
public:
    Owen* _owen;
    void press() const;
    Button(Owen* o) : _owen(o) {}
};