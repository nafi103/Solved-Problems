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
struct Point {
    int x, y;
    void read(){
        cin>>x>>y;
    }
};

pair<int,int> slope(Point &a, Point &b){
    int dy = a.y - b.y;
    int dx = a.x - b.x;
    int g = gcd(dy,dx);
    dy/=g;
    dx/=g;
    if(dy<0){
        dy*= -1;
        dx*=-1;
    }
    return {dy,dx};
}

void solve()
{
    vector<Point>points(4);
    for(int i = 0; i<4; i++){
        points[i].read();
    }
    debug(slope(points[0],points[1]))
    debug(slope(points[2],points[3]))
    if(slope(points[0],points[1])==slope(points[2],points[3])){
        if(slope(points[0],points[1])==slope(points[0],points[3])){
            yes;
        }else{
            no;
        }
    }
    else{
        yes;
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