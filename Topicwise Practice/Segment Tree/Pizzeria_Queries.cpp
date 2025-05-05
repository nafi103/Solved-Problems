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
#define inf 1e14+10
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

struct Segment_Tree{
    int n;
    vector<int>v,st;

    Segment_Tree(vector<int>&_v,int _n){
        n = _n;
        st.resize(4*n,inf);
        v = _v;
        build(1,1,n);
    }
    
    void build(int node, int b, int e){
        if(b==e){
            st[node] = v[b];
            return;
        }
        int mid = (b+e)/2,left = 2*node, right = 2*node+1;
        build(left, b, mid);
        build(right, mid+1,e);
        st[node] = min(st[left]+e-mid,st[right]);
    }
    
    void update(int node, int b, int e, int i, int &value){
        if(e<i or b>i) return;
        if(b==i and e==i){
            st[node] = value;
            return;
        }
        int mid = (b+e)/2,left = 2*node, right = 2*node+1;
        update(left, b, mid, i, value);
        update(right, mid+1 ,e ,i ,value);
        st[node] = min(st[left]+e-mid,st[right]);
    }
    
    int query(int node, int b, int e, int r){
        if(b>r) return inf;
        if(e<=r){
            return st[node];
        }
        int mid = (b+e)/2, left = 2*node, right = 2*node+1;
        if(mid>r){
            return query(left,b,mid,r);
        }
        else    
            return min(query(left,b,mid,r) + min(e,r) - mid ,query(right,mid+1,e,r));
    }
};

void solve()
{
    int n,q;
    cin>>n>>q;
    vector<int>v(n+1);
    for(int i = 1; i<=n; i++){
        cin>>v[i];
    }
    Segment_Tree prefix(v,n);
    reverse(v.begin()+1,v.end());
    Segment_Tree suffix(v,n);
    while(q--){
        int type;
        cin>>type;
        if(type==2){
            int i;
            cin>>i;
            cout<<min(prefix.query(1,1,n,i),suffix.query(1,1,n,n-i+1))<<endl;
        }else{
            int i,val;
            cin>>i>>val;
            prefix.update(1,1,n,i,val);
            suffix.update(1,1,n,n-i+1,val);
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