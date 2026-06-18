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

vector<int>v;
vector<vector<int>>st;
vector<int>lazy;

void build(int node, int b, int e){
    if(b==e){
        for(int i = 0; i<20; i++){
            if(v[b]&(1<<i)) st[node][i]++;
        }
        return;
    }
    int mid = (b+e)/2,left = 2*node, right = 2*node+1;
    build(left, b, mid);
    build(right, mid+1,e);
    for(int i = 0; i<20; i++){
        st[node][i] = st[left][i] + st[right][i];
    }
}

void propagate(int node, int b, int e){
    for(int i = 0; i<20; i++){
        if(lazy[node]&(1<<i)){
            st[node][i] = (e-b+1-st[node][i]);
        }
    }
    if(b!=e){
        lazy[2*node] = lazy[2*node]^lazy[node];
        lazy[2*node+1] = lazy[2*node+1]^lazy[node];
    }
    lazy[node] = 0;
}

void update(int node, int b, int e, int &l, int &r, int &value){
    if(lazy[node]!=0) propagate(node, b, e);
    if(e<l or b>r) return;
    if(b>=l and e<=r){
        for(int i = 0; i<20; i++){
            if(value&(1<<i)){
                st[node][i] = (e-b+1-st[node][i]);
            }
        }
        if(b!=e){
            lazy[2*node]= lazy[2*node]^value;
            lazy[2*node+1] = lazy[2*node+1]^value;
        }
        return;
    }
    int mid = (b+e)/2,left = 2*node, right = 2*node+1;
    update(left, b, mid,l,r,value);
    update(right, mid+1,e,l,r,value);
    for(int i = 0; i<20; i++){
        st[node][i] = st[left][i] + st[right][i];
    }
}

int query(int node, int b, int e, int &l, int &r){
    if(lazy[node]!=0) propagate(node, b, e);
    if(e<l or b>r) return 0;
    if(b>=l and e<=r){
        int ans = 0;
        for(int i = 0; i<20; i++){
            ans+=(st[node][i]*(1<<i));
        }
        return ans;
    }
    int mid = (b+e)/2, left = 2*node, right = 2*node+1;
    return query(left,b,mid,l,r) + query(right,mid+1,e,l,r);
}

void solve()
{
    int n;
    cin>>n;
    st.resize(4*n, vector<int>(20,0));
    lazy.resize(4*n,0);
    v.resize(n+1);
    for(int i = 1; i<=n; i++){
        cin>>v[i];
    }
    build(1,1,n);
    int q;
    cin>>q;
    while(q--){
        int type,l,r;
        cin>>type>>l>>r;
        if(type==1){
            cout<<query(1,1,n,l,r)<<endl;
        }else{
            int x;
            cin>>x;
            update(1,1,n,l,r,x);
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
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}