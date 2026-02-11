#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

struct pt {
    int x, y;
    pt() {}
    pt(int _x, int _y) : x(_x), y(_y) {}
    pt operator-(const pt& p) const { return pt(x - p.x, y - p.y); }
    pt operator+(pt p) const { return pt(x + p.x, y + p.y); }
    int cross(const pt& p) const { return x * p.y - y * p.x; }
    int cross(const pt& a, const pt& b) const { return (a - *this).cross(b - *this); }
    int distance_sq(const pt& p){
        return (p.x - x) * (p.x - x) + (y - p.y) * (y - p.y);
    }
};

bool same(pt a, pt b){
    return a.x == b.x and a.y == b.y;
}

int sgn(const int& x) { return x >= 0 ? x ? 1 : 0 : -1; }

bool inter1(int a, int b, int c, int d) {
    if (a > b)
        swap(a, b);
    if (c > d)
        swap(c, d);
    return max(a, c) <= min(b, d);
}

bool check_intersect(const pt& a, const pt& b, const pt& c, const pt& d) {
    if (c.cross(a, d) == 0 && c.cross(b, d) == 0)
        return inter1(a.x, b.x, c.x, d.x) && inter1(a.y, b.y, c.y, d.y);
    return sgn(a.cross(b, c)) != sgn(a.cross(b, d)) &&
           sgn(c.cross(d, a)) != sgn(c.cross(d, b));
}

const int N = 1e3 + 2;
int n, q;
vector<pt> p(N), tmp(4);

void input(){
    cin >> n >> q;
    for(int i = 0; i < n; i++)
        cin >> p[i].x >> p[i].y;
}

bool boundary(const pt &s){
    int a;
    for(int i = 0; i < n; i++){
        a = 0;
        tmp[0] = tmp[3] = s;
        tmp[1] = p[i]; tmp[2] = p[i + 1];
        for(int j = 0; j < 3; j++){
            a += tmp[j].x * tmp[j + 1].y;
            a -= tmp[j].y * tmp[j + 1].x;
        }
        int minx = min(p[i].x, p[i + 1].x), maxx = max(p[i].x, p[i + 1].x);
        int miny = min(p[i].y, p[i + 1].y), maxy = max(p[i].y, p[i + 1].y);
        if(a == 0 and minx <= s.x and s.x <= maxx and miny <= s.y and s.y <= maxy)
            return true;
    }
    return false;
}

bool inside(const pt &s){
    int intersect = 0;
    pt inf_pt(1e9 + 10, 1e9 + 400);
    for(int i = 0; i < n; i++){
        if(check_intersect(s, inf_pt, p[i], p[i + 1]))
            intersect++;
    }
    return intersect & 1;
}

void solve()
{
    input();
    p[n] = p[0];
    while(q--){
        pt s;
        cin >> s.x >> s.y;
        if(boundary(s)){
            cout << "BOUNDARY" << endl;
        }else if(inside(s)){
            cout << "INSIDE" << endl;
        }else{
            cout << "OUTSIDE" << endl;
        }
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}