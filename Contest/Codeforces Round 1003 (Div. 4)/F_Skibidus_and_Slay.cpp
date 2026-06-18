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
    int n;
    cin>>n;
    vector<int>v(n+1);
    for(int i = 1; i<=n; i++)
        cin>>v[i];
    vector<vector<int>>t(n+1);
    for(int i = 1; i<n; i++){
        int u,v;
        cin>>u>>v;
        t[u].push_back(v);
        t[v].push_back(u);
    }
    vector<bool>majority(n+1,false);
    vector<map<int,int>>mp(n+1);
    for(int i = 1; i<=n; i++){
        for(auto &nbr: t[i]){
            mp[i][v[nbr]]++;
        }
    }
    for(int i = 1; i<=n; i++){
        int &curr = v[i];
        if(majority[curr] or mp[i][curr]){
            majority[curr] = true;
            continue;
        }
        for(auto &nbr: t[i]){
            if(mp[nbr][curr]>1){
                majority[curr] = true;
                break;
            }
        }
    }
    for(int i = 1; i<=n; i++){
        cout<<majority[i];
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