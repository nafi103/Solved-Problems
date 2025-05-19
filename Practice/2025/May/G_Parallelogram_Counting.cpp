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
    
    Point() { x = y = 0 ;}

    Point(int _x, int _y) : x(_x), y(_y) {}
    
    void read(){
        cin>>x>>y;
    }
};

map<array<int,3>,vector<Point>>mp;

int sq(int x){
    return x*x;
}

int dist(const Point &p1, const Point &p2) {
    return sq(p1.x-p2.x) + sq(p1.y-p2.y);
}

pair<int,int>slope(const Point &p1, const Point &p2){
    int sy = p1.y - p2.y;
    int sx = p1.x - p2.x;
    int g = gcd(sy,sx);
    sy/=g;
    sx/=g;
    if(sy==0){
        sx=0;
    }
    if(sy<0){
        sy*=-1;
        sx*=-1;
    }
    return {sy,sx};
}

void slope_and_distance(const Point &p1, const Point &p2){
    int d = dist(p1,p2),sx,sy;
    tie(sy,sx) = slope(p1,p2);
    mp[{sy,sx,d}].push_back(p1);
}

void solve()
{
    mp.clear();
    int n,ans = 0;
    cin>>n;
    vector<Point> points(n);
    for(int i = 0; i<n; i++){
        points[i].read();
    }
    for(int i = 0; i<n-1; i++){
        for(int j = i+1; j<n; j++){
            slope_and_distance(points[i],points[j]);
        }
    }
    for(auto &[f,s]: mp){
        if(sz(s)==1)
            continue;
        auto [sy,sx,d] = f;
        for(int i = 0; i<sz(s)-1; i++){
            for(int j = i+1; j<sz(s); j++){
                if(make_pair(sy,sx)!=slope(s[i],s[j])){
                    ans++;
                }
            }
        }
    }
    cout<<ans/2<<endl;
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