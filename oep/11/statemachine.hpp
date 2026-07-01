#ifndef STATEMACHINE_HPP
#define STATEMACHINE_HPP

#include "threadsafequeue.hpp"
#include <thread>

template <typename Signal, typename State>
class StateMachine
{
public:
    StateMachine();
    virtual ~StateMachine(){ }

    void send(Signal sig){ _eventQueue.enqueue(sig); }

protected:
    State _currentState;
    ThreadSafeQueue<Signal> _eventQueue;
    std::thread _thread;
    bool _life;

    void finalstep();

    void stateMachine();
    Signal getSignal();

    virtual void transition(Signal sig) = 0;
    virtual void initState() = 0;
    virtual bool finalState() const { return !_life; }
};

template <typename Signal, typename State>
StateMachine<Signal, State>::StateMachine() : _life(true)
{
    _eventQueue.startQueue();
    _thread = std::thread(&StateMachine::stateMachine, this);
}

template <typename Signal, typename State>
void StateMachine<Signal, State>::finalstep()
{
    _life = false;
    _eventQueue.stopQueue();
    _thread.join();
}

template <typename Signal, typename State>
Signal StateMachine<Signal, State>::getSignal()
{
    Signal signal;
    _eventQueue.dequeue(signal);
    return signal;
}

template <typename Signal, typename State>
void StateMachine<Signal, State>::stateMachine()
{
    initState();
    while(!finalState()) {
        transition(getSignal());
    }
}

#endif // STATEMACHINE_HPP
