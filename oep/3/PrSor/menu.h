//Készítette:    Veszprémi Anna
//Dátum:         2018.02.20.
//Menürendszer header állomány

#pragma once

#include "priorsor.h"

class Menu
{
    public:
        Menu(){};
        void run();
    private:
        int  getMenuPoint();
        void putIn();
        void removeMax();
        void getMax();
        void checkEmpty();
        void write();
        void test();
        PrQueue pq;

};
