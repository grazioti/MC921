from pathlib import Path
import pytest
from uc.uc_parser import UCParser
from uc.uc_sema import Visitor


def resolve_test_files(test_name):
    input_file = test_name + ".in"
    expected_file = test_name + ".out"

    # get current dir
    current_dir = Path(__file__).parent.absolute()

    # get absolute path to inputs folder
    test_folder = current_dir / Path("in-out")

    # get input path and check if exists
    input_path = test_folder / Path(input_file)
    assert input_path.exists()

    # get expected test file real path
    expected_path = test_folder / Path(expected_file)
    assert expected_path.exists()

    return input_path, expected_path


@pytest.mark.parametrize(
    "test_name",
    [
        "t01",
        "t02",
        "t03",
        "t04",
        "t06",
        "t12",
        "t16",
        "t17",
        "t21",
        "t24",
        "t25",
        "t28",
        "t31",
        "t34",
        "t35",
        "t41",
        "t45",
        "t48",
        "t50",
    ],
)
# capfd will capture the stdout/stderr outputs generated during the test
def test_sema(test_name, capsys):
    input_path, expected_path = resolve_test_files(test_name)

    p = UCParser(debug=False)
    with open(input_path) as f_in, open(expected_path) as f_ex:
        ast = p.parse(f_in.read())
        sema = Visitor()
        sema.visit(ast)
        captured = capsys.readouterr()
        expect = f_ex.read()
    assert captured.out == expect
    assert captured.err == ""


@pytest.mark.parametrize(
    "test_name",
    [
        "t05",
        "t07",
        "t08",
        "t09",
        "t10",
        "t11",
        "t13",
        "t14",
        "t15",
        "t18",
        "t19",
        "t20",
        "t22",
        "t23",
        "t26",
        "t27",
        "t29",
        "t30",
        "t32",
        "t33",
        "t36",
        "t37",
        "t38",
        "t39",
        "t40",
        "t42",
        "t43",
        "t44",
        "t46",
        "t47",
        "t49",
    ],
)
# capfd will capture the stdout/stderr outputs generated during the test
def test_sema_error(test_name, capsys):
    input_path, expected_path = resolve_test_files(test_name)

    p = UCParser(debug=False)
    with open(input_path) as f_in, open(expected_path) as f_ex:
        ast = p.parse(f_in.read())
        sema = Visitor()
        with pytest.raises(SystemExit) as sys_error:
            sema.visit(ast)
        assert sys_error.value.code == 1
        captured = capsys.readouterr()
        expect = f_ex.read()
    assert captured.out == expect
    assert captured.err == ""
