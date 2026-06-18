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
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define endl "\n"
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/


void solve()
{
    int n,m;
    cin>>n>>m;
    vector<int>b(n);
    readv(b);
    vector<vector<pair<int,int>>>g(n);
    int l = 0,r = -inf, save;
    for(int i = 0; i<m; i++){
        int u,v,w;
        cin>>u>>v>>w;
        u--,v--;
        r = max(r,w);
        g[u].push_back({v,w});
    }
    save = r;
    if(m==0){
        cout<<-1<<endl;
        return;
    }
    while(l<=r){
        int mx = (l+r)/2;
        priority_queue<pair<int,int>>q;
        bool reached = false;
        q.push({0,0});
        while(!q.empty()){
            auto [node, battery] = q.top();
            q.pop();
            if(node==n-1){
                reached = true;
                break;
            }
            battery = min(mx, battery+b[node]);
            for(auto &[adj,w]: g[node]){
                if(w<=battery){
                    q.push({adj,battery});
                }
            }
        }
        if(!reached)
            l = mx+1;
        else
            r = mx-1;
    }
    if(l>save)
        cout<<-1<<endl;
    else
        cout<<l<<endl;
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