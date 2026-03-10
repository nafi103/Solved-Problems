#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

struct Node
{
    int value;

    Node(int val = 1) : value(val) {}
};

Node merge(Node &left, Node &right)
{
    if(left.value == inf or right.value == inf or log(left.value) + log(right.value) > log(inf))
        return Node(inf);
    return Node(left.value * right.value);
}

struct Segment_Tree
{
    int n;
    vector<int> v;
    vector<Node> st;

    Segment_Tree(vector<int> &_v, int _n)
    {
        n = _n;
        st.resize(4 * n);
        v = _v;
        build(1, 1, n);
    }

    void build(int node, int b, int e)
    {
        if (b == e)
        {
            st[node] = Node(v[b]);
            return;
        }
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        build(left, b, mid);
        build(right, mid + 1, e);
        st[node] = merge(st[left], st[right]);
    }

    void update(int node, int b, int e, int &idx, Node &value)
    {
        if (e < idx or b > idx)
            return;
        if (b == idx and e == idx)
        {
            st[node] = value;
            return;
        }
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        update(left, b, mid, idx, value);
        update(right, mid + 1, e, idx, value);
        st[node] = merge(st[left], st[right]);
    }

    Node query(int node, int b, int e, int &l, int &r)
    {
        if (e < l or b > r)
            return Node();
        if (b >= l and e <= r)
        {
            return st[node];
        }
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        Node query_left = query(left, b, mid, l, r), query_right = query(right, mid + 1, e, l, r);
        return merge(query_left, query_right);
    }

    int query(int l, int r){
        return query(1, 1, n, l, r).value;
    }
};

const int N = 2e5 + 10;
int pref_sum[N];
map<pair<int,int>,array<int,3>>dp;
vector<int> arr;

array<int, 3> f(int i, int j, Segment_Tree &st){
    if(dp.count({i, j}))
        return dp[{i, j}];
    int save_i = i, save_j = j;
    while(i < j and arr[i] == 1)
        i++;
    while(j > i and arr[j] == 1)
        j--;
    int sum = pref_sum[j] - (i == 0 ? 0 : pref_sum[i - 1]);
    int mul = st.query(i, j);
    if(i == j or mul >= sum){
        return dp[{save_i, save_j}] = {mul - sum, i, j};
    }
    return dp[{save_i, save_j}] = max(f(i + 1, j, st), f(i, j - 1, st));
}

void solve()
{
    arr.clear();
    dp.clear();
    int n;
    cin >> n;
    arr.resize(n + 1);
    for(int i = 1; i <= n; i++){
        cin >> arr[i];
        pref_sum[i] = arr[i] + pref_sum[i - 1];
    }
    if(pref_sum[n] == n){
        cout << 1 << " " << 1 << endl;
        return;
    }
    Segment_Tree st(arr, n);
    auto [mul, l, r] = f(1, n, st);
    cout << l << " " << r << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}