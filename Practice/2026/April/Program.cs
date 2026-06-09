using System;

interface Run {
    void distance(float _time);
}

class Bike : Run {
    string model;
    float accelaration, topSpeed;
    float timeForTopSpeed, distanceForTopSpeed;

    public Bike(float _accelaration, float _topSpeed, string _model) {
        model = _model;
        accelaration = _accelaration;
        topSpeed = _topSpeed;
        // v = u + at ** u = 0
        // t = v / u
        timeForTopSpeed = topSpeed / accelaration;
        distanceForTopSpeed = 0.5f * accelaration * sq(timeForTopSpeed);
    }

    private float sq(float a) {
        return a * a;
    }

    public void distance(float _time) {
        float s = 0f;
        if (_time >= timeForTopSpeed) {
            s += distanceForTopSpeed;
            float remainingTime = _time - timeForTopSpeed;
            s += remainingTime * topSpeed;
        } else {
            s = 0.5f * accelaration * sq(_time);
        }
        Console.WriteLine("I am a bike");
        Console.WriteLine($"Model: {model}.");
        Console.WriteLine($"My top speed is :{topSpeed}");
        Console.WriteLine($"I rode {s:F2} meter");
    }
}

class Speed_Boat : Run {
    string model;
    float accelaration, topSpeed;
    float timeForTopSpeed, distanceForTopSpeed;

    public Speed_Boat(float _accelaration, float _topSpeed, string _model) {
        model = _model;
        accelaration = _accelaration;
        topSpeed = _topSpeed;
        timeForTopSpeed = topSpeed / accelaration;
        distanceForTopSpeed = 0.5f * accelaration * sq(timeForTopSpeed);
    }

    private float sq(float a) {
        return a * a;
    }

    public void distance(float _time) {
        float s = 0f;
        if (_time >= timeForTopSpeed) {
            s += distanceForTopSpeed;
            float remainingTime = _time - timeForTopSpeed;
            s += remainingTime * topSpeed;
        } else {
            s = 0.5f * accelaration * sq(_time);
        }
        Console.WriteLine("This is a speed boat");
        Console.WriteLine($"Model: {model}."); 
        Console.WriteLine($"My top speed is :{topSpeed}");
        Console.WriteLine($"I swim {s:F2} meter");
    }
}

class Cheetah : Run {
    float accelaration, topSpeed;
    float timeForTopSpeed, distanceForTopSpeed;

    public Cheetah(float _accelaration, float _topSpeed) {
        accelaration = _accelaration;
        topSpeed = _topSpeed;
        timeForTopSpeed = topSpeed / accelaration;
        distanceForTopSpeed = 0.5f * accelaration * sq(timeForTopSpeed);
    }

    private float sq(float a) {
        return a * a;
    }

    public void distance(float _time) {
        float s = 0f;
        if (_time >= timeForTopSpeed) {
            s += distanceForTopSpeed;
            float remainingTime = _time - timeForTopSpeed;
            s += remainingTime * topSpeed;
        } else {
            s = 0.5f * accelaration * sq(_time);
        }
        Console.WriteLine("I am a fearless Cheetah");
        Console.WriteLine($"My top speed is :{topSpeed}");
        Console.WriteLine($"I ran {s:F2} meter");
    }
}

class Drone : Run {
    string model;
    float accelaration, topSpeed, maxHeight;
    float timeForTopSpeed, distanceForTopSpeed;

    public Drone(float _accelaration, float _topSpeed, float _maxHeight, string _model) {
        model = _model;
        maxHeight = _maxHeight;
        accelaration = _accelaration;
        topSpeed = _topSpeed;
        timeForTopSpeed = topSpeed / accelaration;
        distanceForTopSpeed = 0.5f * accelaration * sq(timeForTopSpeed);
    }

    private float sq(float a) {
        return a * a;
    }

    public void distance(float _time) {
        float s = 0f;
        if (_time >= timeForTopSpeed) {
            s += distanceForTopSpeed;
            float remainingTime = _time - timeForTopSpeed;
            s += remainingTime * topSpeed;
        } else {
            s = 0.5f * accelaration * sq(_time);
        }
        Console.WriteLine("I am a Drone.");
        Console.WriteLine($"Model: {model}."); 
        Console.WriteLine($"My top speed is :{topSpeed}");
        Console.WriteLine($"I flew {s:F2} meter");
    }
}

class Program {
    static void Main(string[] args) {
        Bike myBike = new Bike(5.0f, 25.0f, "Royal Enfield S350");
        Speed_Boat myBoat = new Speed_Boat(3.0f, 20.0f, "Titanic");
        Cheetah myCheetah = new Cheetah(10.0f, 33.0f);
        Drone myDrone = new Drone(15.0f, 40.0f, 500.0f, "Bayraktar TB2"); 

        Run[] racers = { myBike, myBoat, myCheetah, myDrone };
        
        float testTime = 10.0f;
        
        Console.WriteLine($"--- Race Results for {testTime} seconds ---\n\n");

        for (int i = 0; i < racers.Length; i++) {
            racers[i].distance(testTime); 
            Console.WriteLine("\n\n");
        }
    }
}