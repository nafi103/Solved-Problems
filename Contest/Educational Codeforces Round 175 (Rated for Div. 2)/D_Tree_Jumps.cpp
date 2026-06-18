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


void solve()
{
    int n;
    cin>>n;
    vector<vector<int>>t(n+1);
    for(int i = 2; i<=n; i++){
        int p;
        cin>>p;
        t[p].pb(i);
        t[i].pb(p);
    }
    vector<int>level(n+1,-1);
    queue<pair<int,int>>q;
    level[1] = 0;
    q.push({1,0});
    while(!q.empty()){
        auto [node,lev] = q.front();
        q.pop();
        for(auto &x: t[node]){
            if(level[x]==-1){
                level[x] = lev+1;
                q.push({x,lev+1});
            }
        }
    }
    int max_level = *max_element(all(level));
    vector<int>level_count(max_level+1,0);
    for(int i = 1; i<=n; i++){
        level_count[level[i]]++;
    }
    for(int i = max_level - 1; i>=1; i--){
        level_count[i] = (level_count[i] + ((level_count[i]-1)*level_count[i+1])%mod)%mod;
    }
    cout<<(level_count[0]+level_count[1])%mod<<endl;
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