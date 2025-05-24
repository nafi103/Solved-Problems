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

const double eps = 1e-9;

struct Point {
    double x, y;

    Point() { x = y = 0.0; }

    Point(double _x, double _y) : x(_x), y(_y) {}

    bool operator < (Point other) const {
        if (fabs(x-other.x) > eps)
            return x < other.x;
        return y < other.y;
    }

    bool operator == (const Point &other) const {
        return (fabs(x-other.x) < eps) && (fabs(y-other.y) < eps);
    }

    void read(){
        cin>>x>>y;
    }
};

struct Vector {
    double x, y;
    Vector(double _x, double _y) : x(_x), y(_y) {}
};

Vector toVector(const Point &a, const Point &b) {
    return Vector(b.x-a.x, b.y-a.y);
}

bool in_mid(Point &a, Point &b, Point &c){
    vector<Point> tmp = {a,b,c};
    sort(all(tmp));
    return tmp[1] == c;
}

bool sign(double x){
    return x<eps;
}

double cross(Vector a, Vector b) { return a.x*b.y- a.y*b.x; }

bool intersect(Point &a, Point &b, Point &c, Point &d){
    if (cross(toVector(a, b), toVector(a, c)) == 0 and in_mid(a, b, c)) {
        return true;
    }
    if (cross(toVector(a, b), toVector(a, d)) == 0 and in_mid(a, b, d)) {
        return true;
    }
    if (cross(toVector(c, d), toVector(c, a)) == 0 and in_mid(c, d, a)) {
        return true;
    }
    if (cross(toVector(c, d), toVector(c, b)) == 0 and in_mid(c, d, b)) {
        return true;
    }
    if(sign(cross(toVector(a,b),toVector(a,c)))!=sign(cross(toVector(a,b),toVector(a,d)))
        and sign(cross(toVector(c,d),toVector(c,a)))!=sign(cross(toVector(c,d),toVector(c,b)))){
        return true;
    }
    return false;
}


void solve()
{
    Point p1, p2, r1, r3;
    p1.read();
    p2.read();
    r1.read();
    r3.read();
    Point r2(r2.x,r1.y), r4(r1.x,r2.y);
    int cnt = intersect(p1,p2,r1,r2)+intersect(p1,p2,r3,r2)+intersect(p1,p2,r3,r4)+intersect(p1,p2,r1,r4);
    if((intersect(p1,p2,r1,r3) or intersect(p1,p2,r2,r4)) and cnt>=2){
        cout<<'T';
    }else{
        cout<<'F';
    }
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
        if(z>1)
            cout<<endl;
        solve();
    }
}