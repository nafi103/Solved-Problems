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

int f(int n){
    return (n*(n+1))/2;
}

struct Lazy_Segment_Tree{
    int n;
    vector<int>v,wv,lazy,st,stw;

    Lazy_Segment_Tree(vector<int>&_v,int _n){
        n = _n;
        wv.resize(n+1);
        st.resize(4*n);
        stw.resize(4*n);
        lazy.resize(4*n,0);
        v = _v;
        for(int i = 1; i<=n; i++){
            wv[i] = v[i]*i;
        }
        build(1,1,n);
    }
    
    void build(int node, int b, int e){
        if(b==e){
            st[node] = v[b];
            stw[node] = wv[b];
            return;
        }
        int mid = (b+e)/2,left = 2*node, right = 2*node+1;
        build(left, b, mid);
        build(right, mid+1,e);
        st[node] = st[left]+st[right];
        stw[node] = stw[left]+stw[right];
    }
    
    void propagate(int node, int b, int e){
        st[node]+=((e-b+1)*lazy[node]);
        stw[node]+=(f(e)-f(b-1))*lazy[node];
        if(b!=e){
            lazy[2*node] += lazy[node];
            lazy[2*node+1] += lazy[node];
        }
        lazy[node] = 0;
    }
    
    void update(int node, int b, int e, int &l, int &r, int &value){
        if(lazy[node]!=0) propagate(node, b, e);
        if(e<l or b>r) return;
        if(b>=l and e<=r){
            st[node]+=((e-b+1)*value);
            stw[node]+=(f(e)-f(b-1))*value;
            if(b!=e){
                lazy[2*node] += value;
                lazy[2*node+1] += value;
            }
            return;
        }
        int mid = (b+e)/2,left = 2*node, right = 2*node+1;
        update(left, b, mid,l,r,value);
        update(right, mid+1,e,l,r,value);
        st[node] = st[left]+st[right];
        stw[node] = stw[left]+stw[right];
    }
    
    int query(int node, int b, int e, int &l, int &r){
        if(lazy[node]!=0) propagate(node, b, e);
        if(e<l or b>r) return 0;
        if(b>=l and e<=r){
            return stw[node] - (l-1)*st[node];
        }
        int mid = (b+e)/2, left = 2*node, right = 2*node+1;
        return query(left,b,mid,l,r) + query(right,mid+1,e,l,r);
    }
};


void solve()
{
    int n,q;
    cin>>n>>q;
    vector<int>v(n+1);
    for(int i = 1; i<=n; i++)
        cin>>v[i];
    Lazy_Segment_Tree st(v,n);
    while(q--){
        int t;
        cin>>t;
        if(t==1){
            int l,r,val;
            cin>>l>>r>>val;
            st.update(1,1,n,l,r,val);
        }else{
            int l,r;
            cin>>l>>r;
            cout<<st.query(1,1,n,l,r)<<endl;
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