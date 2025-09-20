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

struct DSU{
    int n;
    vector<int>parent;

    DSU(int _n){
        n = _n;
        parent.resize(n);
        iota(all(parent),0);
    }

    
    int find(int i){ 
        if(parent[i]==i) return i; 
        return parent[i] = find(parent[i]); 
    }
    
    void Union(int a, int b){ 
        a = find(a); 
        b = find(b); 
        if(a==b) return; 
        if(a>b) swap(a,b); //Union by index
        parent[b] = a; 
    }
};


void solve()
{
    int n,m1,m2,u,v;
    cin>>n>>m1>>m2;
    DSU g1(n),g2(n);
    while(m1--){
        cin>>u>>v;
        u--,v--;
        g1.Union(u,v);
    }
    while(m2--){
        cin>>u>>v;
        u--,v--;
        g2.Union(u,v);
    }
    vector<pair<int,int>>ans;
    stack<int> s1,s2;
    for(int j = 1; j<n; j++){
        if(g1.find(j)!=0 and g2.find(j)!=0){
            ans.push_back({0,j});
            g1.Union(0,j);
            g2.Union(0,j);
        }
        if(g1.find(j)!=0)
            s1.push(j);
        if(g2.find(j)!=0)
            s2.push(j);
    }
    while(!s1.empty() and !s2.empty()){
        if(g1.find(s1.top())==0 and g2.find(s1.top())==0){
            s1.pop();
            continue;
        }
        if(g1.find(s2.top())==0 and g2.find(s2.top())==0){
            s2.pop();
            continue;
        }
        ans.push_back({s1.top(),s2.top()});
        g1.Union(s1.top(),s2.top());
        g2.Union(s1.top(),s2.top());
    }
    cout<<sz(ans)<<endl;
    for(auto &[f,s]: ans)
        cout<<f+1<<" "<<s+1<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}