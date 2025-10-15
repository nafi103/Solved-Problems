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
    map<int,int> color_id, leader_color;
    vector<int>parent;

    DSU(int n,vector<int>&v){
        parent.resize(n);
        iota(all(parent),0);
        for(int i = 0; i<n; i++){
            int &color = v[i];
            if(color_id.count(color))
                Union(color_id[color],i);
            else{
                color_id[color] = i;
                leader_color[i] = color;
            }
        }
    }
 
    int find(int i){ 
        if(parent[i]==i) return i; 
        return parent[i] = find(parent[i]); 
    }

    void change_color(int prev_color, int color){
        if(color_id.count(prev_color)==0 or prev_color==color)
            return;
        int id = color_id[prev_color];
        if(color_id.count(color)){
            leader_color.erase(id);
            color_id.erase(prev_color);
            int new_color_leader = color_id[color];
            parent[id] = new_color_leader;
        }else{
            leader_color[id] = color;
            color_id.erase(prev_color);
            color_id[color] = id;
        }
    }

    void query(int id){
        id = find(id);
        cout<<leader_color[id]<<endl;
    }
    
    void Union(int a, int b){ 
        a = find(a); 
        b = find(b); 
        if(a==b) return;
        parent[b] = a;
    }
};

void solve()
{
    int n,q;
    cin>>n>>q;
    vector<int>v(n);
    readv(v);
    DSU uf(n,v);
    while(q--){
        int t;
        cin>>t;
        if(t==1){
            int x,y;
            cin>>x>>y;
            uf.change_color(x,y);
        }else{
            int id;
            cin>>id;
            id--;
            uf.query(id);
        }
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
        cout<<"Case "<<z<<":\n";
        solve();
    }
}