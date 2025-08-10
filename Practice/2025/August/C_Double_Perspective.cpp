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
    vector<int>parent, _size;

    DSU(int n){
        parent.resize(n);
        iota(all(parent),0);
        _size.assign(n,1); 
    }
 
    int find(int i){ 
        if(parent[i]==i) return i; 
        return parent[i] = find(parent[i]); 
    } 
    
    int size(int a){ 
        a = find(a); 
        return _size[a]; 
    }
    
    bool Union(int a, int b){ 
        a = find(a); 
        b = find(b); 
        if(a==b) return false; 
        if(_size[a]<_size[b]) swap(a,b);
        parent[b] = a; 
        _size[a]+=_size[b]; 
        return true;
    }
};

void solve()
{
    int n;
    cin>>n;
    DSU uf(2*n+1);
    struct Node{
        int a,b,id;
        Node(int &_a, int &_b, int &_id) : a(_a), b(_b), id(_id){}
    };
    vector<Node> edges;
    for(int i = 1; i<=n; i++){
        int l,r;
        cin>>l>>r;
        edges.push_back(Node(l,r,i));
    }
    sort(all(edges),[&](Node &n1, Node &n2){
        return n1.b - n1.a > n2.b - n2.a;
    });
    vector<int>ans;
    for(auto &x: edges){
        int u = x.a, v = x.b, id = x.id;
        if(uf.Union(u,v)){
            ans.push_back(id);
        }
    }
    sort(all(ans));
    cout<<sz(ans)<<endl;
    for(auto &x: ans)
        cout<<x<<" ";
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