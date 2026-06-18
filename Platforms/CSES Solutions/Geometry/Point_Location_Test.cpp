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
    void read(){
        cin>>x>>y;
    }
    bool operator == (const Point &other) const {
    return (fabs(x-other.x) < EPS) && (fabs(y-other.y) < EPS);
    }
};

struct vec { double x, y;
    vec(double _x, double _y) : x(_x), y(_y) {}
};

vec toVec(const Point &a, const Point &b) {
    return vec(b.x-a.x, b.y-a.y);
}
double cross(vec a, vec b) { return a.x*b.y - a.y*b.x; }

bool ccw(Point p, Point q, Point r) {
    return cross(toVec(p, q), toVec(p, r)) > EPS;
}

bool collinear(Point p, Point q, Point r) {
    return fabs(cross(toVec(p, q), toVec(p, r))) < EPS;
}

void solve()
{
    vector<Point> points(3);
    for(int i = 0; i<3; i++){
        points[i].read();
    }
    if(collinear(points[0],points[1],points[2])){
        cout<<"TOUCH"<<endl;
        return;
    }
    if(ccw(points[0],points[1],points[2])){
        cout<<"LEFT"<<endl;
    }else{
        cout<<"RIGHT"<<endl;
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
        // google(z);
        solve();
    }
}