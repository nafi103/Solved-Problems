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

struct S{
    int operation;
    vector<int>v, pref;
    S(){
        operation = 0;
        v = {};
        pref = {};
    }
    S(int val){
        operation = 0;
        v = {val};
        pref = {val};
    }
};

S combine(S &a, S &b){
    S temp = a;
    if(temp.v.empty()){
        return b;
    }
    temp.operation+=b.operation;
    for(auto &x: b.v){
        if(x<temp.v.back()){
            temp.operation+=(temp.v.back()-x);
            temp.v.push_back(temp.v.back());
        }else{
            temp.v.push_back(x);
        }
        temp.pref.push_back(temp.pref.back()+temp.v.back());
    }
    return temp;
}

struct Segment_Tree{
    int n;
    vector<S>t;
    vector<int>v;

    Segment_Tree(int _n){
        n = _n;
        t.resize(4*n);
        v.resize(n+1);
    }

    void place(){
        for(int i = 1; i<=n; i++){
            cin>>v[i];
        }
        build(1,1,n);
    }

    void build(int node, int b, int e){
        if(b==e){
            t[node] = S(v[b]);
            return;
        }
        int mid = (b+e)/2, left = 2*node, right = 2*node+1;
        build(left,b,mid);
        build(right,mid+1,e);
        t[node] = combine(t[left],t[right]);
    }

    array<int,3> find_node(int node, int b, int e, int &l, int &r){
        if(b==l and e<=r){
            return {node,b,e};
        }
        int mid = (b+e)/2, left = 2*node, right = 2*node+1;
        if(mid<l)
            return find_node(right, mid+1, e,l,r);
        return find_node(left,b,mid,l,r);
    }

    int query(int l, int r){
        auto [node,b,ex] = find_node(1,1,n,l,r);
        int e = ex+1;
        int operation = t[node].operation, mx = t[node].v.back();
        while(e<=r){
            auto [nodep, bp, ep] = find_node(1,1,n,e,r);
            operation+=t[nodep].operation;
            vector<int> &v = t[nodep].v;
            int p = 0, q = sz(v) - 1;
            while(p<=q){
                int mid = (p+q)/2;
                if(v[mid]<mx){
                    p = mid+1;
                }else{
                    q = mid-1;
                }
            }
            if(q==-1){
                mx = v.back();
                e = ep+1;
                continue;
            }
            operation+=((q+1)*mx-t[nodep].pref[q]);
            mx = max(mx,v.back());
            e = ep+1;
        }
        return operation;
    }
};

void solve()
{
    int n,q;
    cin>>n>>q;
    Segment_Tree st(n);
    st.place();
    while(q--){
        int l,r;
        cin>>l>>r;
        cout<<st.query(l,r)<<endl;
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