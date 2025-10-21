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
const int N = 4e5+10, D = 2e5;

void solve()
{
    int n,m,q,x,ax;
    cin>>n>>m>>q;
    vector<int>a(n),b(m);
    readv(a);
    readv(b);
    int suma = accumulate(all(a),0ll), sumb = accumulate(all(b),0ll);
    bitset<N>fa,fb;
    for(auto &y: a){
        if(abs(suma-y)>D)
            continue;
        fa[suma-y+D] = 1;
    }
    for(auto &y: b){
        if(abs(sumb-y)>D)
            continue;
        fb[sumb-y+D] = 1;
    }
    while(q--){
        cin>>x;
        ax = abs(x);
        vector<int>divisors;
        for(int i = 1; i*i<=ax; i++){
            if(ax%i==0){
                divisors.push_back(i);
                if(ax/i!=i)
                    divisors.push_back(ax);
            }
        }
        sort(all(divisors));
        bool flag = false;
        for(auto &d: divisors){
            if(ax/d>D)
                continue;
            flag|=(fa[d+D]&fb[x/d + D]);
            flag|=(fa[-d+D]&fb[-(x/d) + D]);
            flag|=(fb[d+D]&fa[x/d + D]);
            flag|=(fb[-d+D]&fa[-(x/d) + D]);
            if(flag)
                break;
        }
        cout<<(flag?"YES":"NO")<<endl;
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