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

struct DSU{
    int n;
    vector<int>parent, _size;

    DSU(int &_n){
        n = _n;
        parent.resize(n);
        iota(all(parent),0);
        _size.assign(n,1); 
    }
 
    int find(int i){ 
        if(parent[i]==i) return i; 
        return parent[i] = find(parent[i]); 
    }

    bool connected(){
        return _size[find(0)]==n;
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
    }
};
 
void solve(){
    int n,k; 
    cin>>n>>k;
    set<array<int,3>>s;
    while(k--){ 
        int u,v,w, ans = 0; 
        cin>>u>>v>>w;
        u--,v--;
        s.insert({w,u,v});
        auto ers = s.end();
        DSU uf(n);
        for(auto it = s.begin(); it!=s.end(); it++){
            auto &[wt,x,y] = *it;
            if(uf.find(x)!=uf.find(y)){
                ans+=wt;
                uf.Union(x,y);
            }else{
                ers = it;
            }
        }
        if(ers!=s.end())
            s.erase(ers);
        if(uf.connected())
            cout<<ans<<endl;
        else cout<<-1<<endl;
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
    cin>>t;
    for(int z = 1; z<=t; z++){
        cout<<"Case "<<z<<":\n";
        solve();
    }
}