#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18+10
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define writev(v)     \
    for (auto &x : v) \
    cout << x << " "; \
    cout<<endl
#define endl "\n"
#define yes cout<<"YES"<<endl
#define no cout<<"NO"<<endl
#define remove_punctuation(text) regex_replace(text, regex(R"([^\w\s])"), "")
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

const double EPS = 1e-9;

struct Point {
    double x, y;

    Point() { x = y = 0.0; }

    Point(double _x, double _y) : x(_x), y(_y) {}

    bool operator < (Point other) const {
        if (fabs(x-other.x) > EPS)
            return x < other.x;
        return y < other.y;
    }

    bool operator == (const Point &other) const {
        return (fabs(x-other.x) < EPS) && (fabs(y-other.y) < EPS);
    }

    void read(){
        cin>>x>>y;
    }
};

double dist(const Point &p1, const Point &p2) {
    return hypot(p1.x-p2.x, p1.y-p2.y);
}

double DEG_to_RAD(double d) { return d*pi / 180.0; }

double RAD_to_DEG(double r) { return r*180.0 / pi; }

Point rotate(const Point &p, double theta) {
    double rad = DEG_to_RAD(theta);
    return Point(p.x*cos(rad)- p.y*sin(rad),p.x*sin(rad) + p.y*cos(rad));
}

struct Vector {
    double x, y;
    Vector(double _x, double _y) : x(_x), y(_y) {}
};

Vector toVector(const Point &a, const Point &b) {
    return Vector(b.x-a.x, b.y-a.y);
}

Vector scale(const Vector &v, double s) {
    return Vector(v.x * s, v.y * s);
}

Point translate(const Point &p, const Vector &v) {
    return Point(p.x + v.x, p.y + v.y);
}


void solve()
{
    Point a,b;
    a.read();
    b.read();
    double M,L;
    cin>>M>>L;
    Vector ba = toVector(b,a);
    ba  = scale(ba,L/dist(b,a));
    Point c;
    c = translate(c,ba);
    c = rotate(c,M);
    c.x+=b.x;
    c.y+=b.y;
    cout<<(int)round(c.x)<<" "<<(int)round(c.y)<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}