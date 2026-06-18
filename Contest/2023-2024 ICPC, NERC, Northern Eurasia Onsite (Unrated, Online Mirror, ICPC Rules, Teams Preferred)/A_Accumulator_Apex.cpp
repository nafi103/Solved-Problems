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
    int mn, mx;
     Node(){
        mn = inf;
        mx = -inf;
    }
     Node(int val){
        mn = mx = val;
    }
};
 Node merge(Node &left, Node &right)
{
    Node res;
    res.mn = min(left.mn, right.mn);
    res.mx = max(left.mx, right.mx);
    return res;
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
        for(int i = 1; i <= n; i++)
            v[i] = (v[i - 1] + v[i]);
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
      Node query(int l, int r){
        return query(1, 1, n, l, r);
    }
     int next_greater(int i){
        int x = v[i - 1];
        int l = i, r = n;
        while(l <= r){
            int mid = (l + r) / 2;
            if(query(i + 1, mid).mx > x)
                r = mid - 1;
            else
                l = mid + 1;
        }
        if(l > n)
            return -1;
        return l;
    }
};
 void solve()
{
    int init, k;
    cin >> init >> k;
    vector<int> p(k, 1);
    vector<vector<int>> grid(k);
    vector<Segment_Tree> st;
    for(int i = 0; i < k; i++){
        int n;
        cin >> n;
        grid[i].resize(n + 1);
        grid[i][0] = 0;
        for(int j = 1; j <= n; j++){
            cin >> grid[i][j];
        }
        st.push_back(Segment_Tree(grid[i], n));
    }
    for(int i = 0; i < k; i++){
        while(p[i] < sz(grid[i]) and grid[i][p[i]] >= 0){
            init += grid[i][p[i]];
            p[i]++;
        }
    }
    int ans = init;
    priority_queue<array<int,3>> pq;
    for(int i = 0; i < k; i++){
        if(p[i] < sz(grid[i])){
            int l = p[i];
            int r = st[i].next_greater(l);
            if(r == -1)
                continue;
            else{
                pq.push({st[i].query(l, r).mn - st[i].v[l - 1], r , i});
            }
        }
    }
    while(!pq.empty()){
        auto [mn, r, i] = pq.top();
        pq.pop();
        if(init + mn < 0)
            break;
        while(r + 1 < sz(grid[i]) and grid[i][r] >= 0 and grid[i][r + 1] >= 0)
            r++;
        init += st[i].v[r] - st[i].v[p[i] - 1];
        p[i] = r + 1;
        if(p[i] < sz(grid[i])){
            int ll = p[i];
            int rr = st[i].next_greater(ll);
            if(rr == -1)
                continue;
            else
                pq.push({st[i].query(ll, rr).mn - st[i].v[ll - 1], rr , i});
        }
    }
    cout << init << endl;
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}