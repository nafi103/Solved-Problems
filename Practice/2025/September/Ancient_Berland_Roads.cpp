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
    vector<vector<int>>population;
    vector<int>parent, _size, total_population;
    multiset<int>region_population;

    DSU(int _n){
        n = _n;
        parent.resize(n);
        iota(all(parent),0);
        _size.assign(n,1); 
        population.resize(n);
        total_population.resize(n);
    }

    void assign_population(){
        for(int i = 0; i<n; i++){
            total_population[i] = population[i].back();
            region_population.insert(total_population[i]);
        }
    }

    int find(int i){ 
        if(parent[i]==i) return i; 
        return parent[i] = find(parent[i]); 
    } 
    
    void update_population(int i){
        int p = find(i);
        int old = population[i].back();
        population[i].pop_back();
        int now = population[i].back();
        region_population.erase(region_population.find(total_population[p]));
        total_population[p] += (now-old);
        region_population.insert(total_population[p]);
    }

    int size(int a){ 
        a = find(a); 
        return _size[a]; 
    }
    
    void Union(int a, int b){ 
        a = find(a); 
        b = find(b); 
        if(a==b) return; 
        if(_size[a]<_size[b]) swap(a,b);
        parent[b] = a; 
        _size[a]+=_size[b];
        region_population.erase(region_population.find(total_population[a]));
        region_population.erase(region_population.find(total_population[b]));
        total_population[a]+=total_population[b];
        region_population.insert(total_population[a]);
    }
};

struct Query
{
    int t, index;
    Query(int _t, int &_index){
        t = _t;
        index = _index;
    }
    Query(){
        t = 0;
        index = 0;
    }
};


void solve()
{
    int n,m,q;
    cin>>n>>m>>q;
    DSU uf(n);
    for(int i = 0; i<n; i++){
        int x;
        cin>>x;
        uf.population[i].push_back(x);
    }
    vector<int>take(m,true);
    vector<pair<int,int>>edges(m);
    for(auto &[f,s]:edges){
        cin>>f>>s;
        f--,s--;
    }
    vector<Query>query(q);
    for(int i = 0; i<q; i++){
        char t;
        cin>>t;
        if(t=='P'){
            int id,p;
            cin>>id>>p;
            id--;
            uf.population[id].push_back(p);
            query[i] = {1,id};
        }else{
            int road;
            cin>>road;
            road--;
            take[road] = false;
            query[i] = {0,road};
        }
    }
    uf.assign_population();
    for(int i = 0; i<m; i++){
        if(take[i]){
            uf.Union(edges[i].first,edges[i].second);
        }
    }
    vector<int>ans;
    ans.reserve(q);
    while(!query.empty()){
        ans.push_back(*uf.region_population.rbegin());
        int x = query.back().t, y = query.back().index;
        query.pop_back();
        if(x){
            uf.update_population(y);
        }else{
            uf.Union(edges[y].first,edges[y].second);
        }
    }
    reverse(all(ans));
    for(auto &x:ans){
        cout<<x<<endl;
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
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}