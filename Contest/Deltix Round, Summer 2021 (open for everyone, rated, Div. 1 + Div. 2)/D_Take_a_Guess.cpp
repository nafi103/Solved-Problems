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
// #define endl "\n"
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

void _or(int a, int b){
    cout<<"or "<<a<<" "<<b<<endl;
}

void _and(int a, int b){
    cout<<"and "<<a<<" "<<b<<endl;
}

int sum(int a, int b){
    int a_and_b, a_or_b;
    _and(a,b);
    cin>>a_and_b;
    _or(a,b);
    cin>>a_or_b;
    int a_xor_b = a_or_b - a_and_b;
    return 2*a_and_b + a_xor_b;
}


void solve()
{
    int n,k;
    cin>>n>>k;
    int sum_ab = sum(1,2), sum_bc = sum(2,3), sum_ac = sum(1,3);
    int sum_abc = (sum_ab+sum_bc+sum_ac)/2;
    int a = sum_abc - sum_bc, b = sum_abc - sum_ac, c = sum_abc - sum_ab;
    vector<int>values = {a,b,c};
    for(int i = 4; i<=n; i++){
        int sum_ax = sum(1,i);
        values.pb(sum_ax-a);
    }
    sort(all(values));
    cout<<"finish "<<values[k-1]<<endl;
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