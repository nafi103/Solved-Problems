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
    int n,m,l, mnodd = inf, sum = 0;
    cin>>n>>m>>l;
    for(int i = 0; i<l; i++){
        int x;
        cin>>x;
        sum+=x;
        if(x&1)
            mnodd = min(mnodd,x);
    }
    vector<int>mx(2, -inf);
    mx[(sum&1)] = sum;
    if(mnodd!=inf)
        mx[((sum-mnodd)&1)] = sum-mnodd;
    vector<vector<int>>g(n+1);
    while(m--){
        int u,v;
        cin>>u>>v;
        g[u].push_back(v);
        g[v].push_back(u);
    }
    vector<vector<int>> distance(n+1,vector<int>(2,inf));
    distance[1][0] = 0;distance[1][1] = inf;
    priority_queue<pair<int,int>,vector<pair<int,int>>,greater<pair<int,int>>>q;
    q.push({0,1});
    while(!q.empty()){
        auto [dis,node] = q.top();
        q.pop();
        int d = dis+1, parity = d&1;
        for(auto &nbr: g[node]){
            if(distance[nbr][parity]>d){
                distance[nbr][parity] = d;
                q.push({d,nbr});
            }
        }
    }
    for(int i = 1; i<=n; i++){
        bool flag = false;
        for(int j = 0; j<2; j++){
            if(distance[i][j]!=inf and distance[i][j]<=mx[j])
                flag = true;
        }
        cout<<flag;
    }
    cout<<endl;
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