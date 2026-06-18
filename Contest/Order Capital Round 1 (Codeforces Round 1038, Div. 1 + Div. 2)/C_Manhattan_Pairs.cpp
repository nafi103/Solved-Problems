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

struct Point{
    int x,y,id;
    Point(){
        x = 0, y = 0, id = -1;
    }
};

bool cmp(Point &a, Point &b){
    if(a.x!=b.x)
        return a.x<b.x;
    return a.y<b.y;
}

void solve()
{
    int n;
    cin>>n;
    vector<Point>point(n);
    Point center;
    for(int i = 0; i<n; i++){
        cin>>point[i].x>>point[i].y;
        point[i].id = i;
    }
    sort(all(point),[&](Point &a, Point &b){
        if(a.y!=b.y)
            return a.y<b.y;
        return a.x<b.x;
    });
    sort(point.begin(),point.begin()+n/2,cmp);
    sort(point.begin()+n/2,point.end(),cmp);
    for(int i = 0; i<n/2; i++){
        cout<<point[i].id+1<<" "<<point[n-1-i].id+1<<endl;
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
        // cout<<"Case "<<z<<": ";
        solve();
    }
}