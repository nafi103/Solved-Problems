#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 1e9+7;
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

struct Lazy_Segment_Tree{
    int n;
    vector<int>lazy,st;

    Lazy_Segment_Tree(int _n){
        n = _n;
        st.resize(4*n);
        lazy.resize(4*n,0);
    }
    
    void propagate(int node, int b, int e){
        st[node]=(st[node]|lazy[node]);
        if(b!=e){
            lazy[2*node] = (lazy[2*node]|lazy[node]);
            lazy[2*node+1] = (lazy[2*node+1]|lazy[node]);
        }
        lazy[node] = 0;
    }
    
    void update(int node, int b, int e, int &l, int &r, int &value){
        if(lazy[node]!=0) propagate(node, b, e);
        if(e<l or b>r) return;
        if(b>=l and e<=r){
            st[node]=(st[node]|value);
            if(b!=e){
                lazy[2*node] = (lazy[2*node]|value);
                lazy[2*node+1] = (lazy[2*node+1]|value);
            }
            return;
        }
        int mid = (b+e)/2,left = 2*node, right = 2*node+1;
        update(left, b, mid,l,r,value);
        update(right, mid+1,e,l,r,value);
        st[node] = (st[left]&st[right]);
    }
    
    int query(int node, int b, int e, int &l, int &r){
        if(lazy[node]!=0) propagate(node, b, e);
        if(e<l or b>r) return LLONG_MAX;
        if(b>=l and e<=r){
            return st[node];
        }
        int mid = (b+e)/2, left = 2*node, right = 2*node+1;
        return (query(left,b,mid,l,r) & query(right,mid+1,e,l,r));
    }
};


void solve()
{
    int n,q;
    cin>>n>>q;
    Lazy_Segment_Tree st(n);
    while(q--){
        int type,l,r;
        cin>>type>>l>>r;
        l++;
        if(type==1){
            int val;
            cin>>val;
            st.update(1,1,n,l,r,val);
        }else{
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