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

struct Vector {
    double x, y;
    Vector(double _x, double _y) : x(_x), y(_y) {}
};

Vector toVector(const Point &a, const Point &b) {
    return Vector(b.x-a.x, b.y-a.y);
}

double dot(Vector a, Vector b) { return (a.x*b.x + a.y*b.y); }

double norm_sq(Vector v) { return v.x*v.x + v.y*v.y; }

double angle(const Point &a, const Point &o, const Point &b) {
    Vector oa = toVector(o, a), ob = toVector(o, b);
    return acos(dot(oa, ob) / sqrt(norm_sq(oa) * norm_sq(ob)));
}

void solve()
{
    Point o,a,b;
    o.read();
    a.read();
    b.read();
    cout<<dist(o,a)*angle(a,o,b)<<endl;
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
        cout<<"Case "<<z<<": ";
        solve();
    }
}